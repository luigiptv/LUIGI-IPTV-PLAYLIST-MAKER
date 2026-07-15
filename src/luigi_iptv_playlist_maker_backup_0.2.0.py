from __future__ import annotations
import os, re, shutil, subprocess, threading, time, urllib.request, urllib.error
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_NAME='LUIGI IPTV PLAYLIST MAKER'; VERSION='0.2.0'
@dataclass
class Channel: extinf:str; url:str; name:str

def read_text(path):
    for enc in ('utf-8-sig','utf-8','cp1250','latin-1'):
        try:return path.read_text(encoding=enc)
        except UnicodeDecodeError:pass
    return path.read_text(encoding='utf-8',errors='replace')

def parse(path):
    out=[]; ext=''
    for raw in read_text(path).splitlines():
        s=raw.strip()
        if not s: continue
        if s.startswith('#EXTINF'): ext=s
        elif s.startswith('#'): continue
        elif '://' in s:
            name=ext.rsplit(',',1)[-1].strip() if ',' in ext else s
            out.append(Channel(ext or f'#EXTINF:-1,{name}',s,name)); ext=''
    return out

def dedupe(items):
    keep=[]; removed=[]; urls=set(); names=set()
    for c in items:
        u=c.url.casefold().strip(); n=re.sub(r'\s+',' ',c.name).casefold().strip()
        if u in urls: removed.append((c,'DUPLICATE_URL')); continue
        if n and n in names: removed.append((c,'DUPLICATE_NAME')); continue
        urls.add(u); names.add(n); keep.append(c)
    return keep,removed

def ffprobe_path():
    for p in (shutil.which('ffprobe'),r'C:\ffmpeg-8.1.2-essentials_build\bin\ffprobe.exe',str(Path.cwd()/'ffprobe.exe')):
        if p and Path(p).is_file(): return p

def classify(text):
    t=text.casefold()
    if '401' in t or '403' in t or 'unauthorized' in t or 'forbidden' in t:return 'AUTH_OR_GEO'
    if '404' in t or 'not found' in t:return 'NOT_FOUND'
    if 'timeout' in t or 'timed out' in t:return 'TIMEOUT'
    if 'resolve' in t or 'no such host' in t:return 'DNS_ERROR'
    if 'connection refused' in t:return 'CONNECTION_REFUSED'
    return 'DEAD'

def test(c,timeout,ffprobe,stop):
    start=time.monotonic()
    if stop.is_set(): return c,'STOPPED','Přerušeno',0
    if ffprobe:
        cmd=[ffprobe,'-v','error','-user_agent','Mozilla/5.0','-rw_timeout',str(timeout*1000000),'-show_entries','format=format_name','-of','default=noprint_wrappers=1:nokey=1',c.url]
        try:
            r=subprocess.run(cmd,capture_output=True,text=True,timeout=timeout+3,creationflags=subprocess.CREATE_NO_WINDOW if os.name=='nt' else 0)
            e=time.monotonic()-start
            if r.returncode==0:return c,('SLOW' if e>=timeout*.75 else 'OK'),f'{e:.1f}s',e
            reason=(r.stderr or 'ffprobe error').strip().splitlines()[-1][:240]
            return c,classify(reason),reason,e
        except subprocess.TimeoutExpired:return c,'TIMEOUT',f'Timeout {timeout}s',time.monotonic()-start
        except Exception as ex:return c,classify(str(ex)),str(ex)[:240],time.monotonic()-start
    req=urllib.request.Request(c.url,headers={'User-Agent':'Mozilla/5.0'})
    try:
        with urllib.request.urlopen(req,timeout=timeout) as r:
            r.read(256); e=time.monotonic()-start
            return c,('SLOW' if e>=timeout*.75 else 'OK'),f'HTTP {getattr(r,"status",200)}',e
    except Exception as ex:return c,classify(str(ex)),str(ex)[:240],time.monotonic()-start

def save_m3u(path,items):
    lines=['#EXTM3U']
    for c in items: lines += [c.extinf,c.url]
    path.write_text('\n'.join(lines)+'\n',encoding='utf-8-sig')

class App(tk.Tk):
    def __init__(self):
        super().__init__(); self.title(f'{APP_NAME} {VERSION}'); self.geometry('900x620'); self.file=None; self.running=False; self.stop_event=threading.Event()
        self.file_var=tk.StringVar(value='Není vybrán playlist'); self.status=tk.StringVar(value='Připraveno'); self.progress=tk.DoubleVar(); self.test_var=tk.BooleanVar(value=True); self.timeout=tk.IntVar(value=8); self.workers=tk.IntVar(value=15)
        ttk.Label(self,text=APP_NAME,font=('Segoe UI',20,'bold')).pack(pady=(16,2)); ttk.Label(self,text=f'Testovací verze {VERSION}').pack()
        r=ttk.Frame(self); r.pack(fill='x',padx=24,pady=16); ttk.Button(r,text='Vybrat playlist',command=self.choose).pack(side='left'); ttk.Label(r,textvariable=self.file_var).pack(side='left',padx=12)
        o=ttk.LabelFrame(self,text='Nastavení'); o.pack(fill='x',padx=24); ttk.Checkbutton(o,text='Testovat dostupnost streamů',variable=self.test_var).grid(row=0,column=0,padx=12,pady=10); ttk.Label(o,text='Timeout').grid(row=0,column=1); ttk.Spinbox(o,from_=3,to=30,width=5,textvariable=self.timeout).grid(row=0,column=2); ttk.Label(o,text='Současné testy').grid(row=0,column=3,padx=(20,4)); ttk.Spinbox(o,from_=1,to=40,width=5,textvariable=self.workers).grid(row=0,column=4)
        b=ttk.Frame(self); b.pack(pady=15); self.start_btn=ttk.Button(b,text='SMART FIX – SPUSTIT',command=self.start); self.start_btn.pack(side='left',ipadx=25,ipady=7,padx=5); self.stop_btn=ttk.Button(b,text='STOP',command=self.stop,state='disabled'); self.stop_btn.pack(side='left',ipadx=15,ipady=7,padx=5)
        ttk.Progressbar(self,variable=self.progress,maximum=100).pack(fill='x',padx=24); ttk.Label(self,textvariable=self.status).pack(pady=7)
        f=ttk.LabelFrame(self,text='Průběh'); f.pack(fill='both',expand=True,padx=24,pady=(0,12)); self.log=tk.Text(f,state='disabled',wrap='word'); self.log.pack(fill='both',expand=True,padx=8,pady=8)
        ttk.Label(self,text=f'{APP_NAME} – Verze {VERSION} – © 2026 Luigis.cz').pack(pady=(0,10))
    def choose(self):
        p=filedialog.askopenfilename(filetypes=[('M3U playlist','*.m3u *.m3u8'),('Všechny soubory','*.*')])
        if p:self.file=Path(p); self.file_var.set(p); self.write(f'Vybrán: {p}')
    def write(self,s):
        self.log.config(state='normal'); self.log.insert('end',s+'\n'); self.log.see('end'); self.log.config(state='disabled')
    def ui(self,func,*args): self.after(0,func,*args)
    def stop(self): self.stop_event.set(); self.write('Zastavuji po dokončení právě běžících testů...')
    def start(self):
        if self.running:return
        if not self.file:return messagebox.showwarning('Chybí playlist','Nejprve vyber playlist.')
        self.running=True; self.stop_event.clear(); self.start_btn.config(state='disabled'); self.stop_btn.config(state='normal'); threading.Thread(target=self.process,daemon=True).start()
    def process(self):
        try:
            stamp=datetime.now().strftime('%Y%m%d_%H-%M-%S'); src=self.file; out=src.parent/f'LUIGI_OUTPUT_{stamp}'; out.mkdir(exist_ok=True); backup=out/f'{src.stem}_backup_{stamp}{src.suffix}'; shutil.copy2(src,backup)
            items=parse(src); unique,dups=dedupe(items); self.ui(self.write,f'Načteno: {len(items)} streamů'); self.ui(self.write,f'Záloha vytvořena: {backup.name}'); self.ui(self.write,f'Duplicity odstraněny: {len(dups)}')
            results=[]; working=[]
            if self.test_var.get():
                ff=ffprobe_path(); workers=max(1,min(40,self.workers.get())); timeout=max(3,self.timeout.get()); self.ui(self.write,f'Metoda: {"ffprobe" if ff else "HTTP"}, současně: {workers}, timeout: {timeout}s'); started=time.monotonic()
                with ThreadPoolExecutor(max_workers=workers) as ex:
                    futures=[ex.submit(test,c,timeout,ff,self.stop_event) for c in unique]
                    for i,f in enumerate(as_completed(futures),1):
                        r=f.result(); results.append(r)
                        if r[1] in ('OK','SLOW'):working.append(r[0])
                        elapsed=max(.01,time.monotonic()-started); eta=int((len(unique)-i)/(i/elapsed)) if i else 0; self.ui(self.progress.set,i/len(unique)*100); self.ui(self.status.set,f'Testování: {i} z {len(unique)} | Ponecháno: {len(working)} | ETA: {eta}s')
                        if self.stop_event.is_set(): break
            else: working=unique; self.ui(self.progress.set,100)
            clean=out/f'{src.stem}_LUIGI_OK_{stamp}.m3u'; save_m3u(clean,working)
            (out/f'{src.stem}_duplicates_{stamp}.txt').write_text('\n'.join(f'[{r}] {c.name}\n{c.url}' for c,r in dups),encoding='utf-8-sig')
            (out/f'{src.stem}_working_{stamp}.txt').write_text('\n'.join(f'[{s}] {c.name}\n{c.url}\n{reason}' for c,s,reason,_ in results if s in ('OK','SLOW')) if results else '\n'.join(f'[NOT_TESTED] {c.name}\n{c.url}' for c in working),encoding='utf-8-sig')
            (out/f'{src.stem}_removed_{stamp}.txt').write_text('\n'.join(f'[{s}] {c.name}\n{c.url}\n{reason}' for c,s,reason,_ in results if s not in ('OK','SLOW','STOPPED')),encoding='utf-8-sig')
            counts={}
            for _,s,_,_ in results:counts[s]=counts.get(s,0)+1
            (out/'summary.txt').write_text(f'Celkem: {len(items)}\nDuplicity: {len(dups)}\nOK: {counts.get("OK",0)}\nPomalé: {counts.get("SLOW",0)}\nTimeout: {counts.get("TIMEOUT",0)}\nAutentizace/Geo: {counts.get("AUTH_OR_GEO",0)}\n404: {counts.get("NOT_FOUND",0)}\nOstatní mrtvé: {counts.get("DEAD",0)}\nPonecháno: {len(working)}\nVýstup: {clean}\n',encoding='utf-8-sig')
            self.ui(self.write,f'Výstup: {clean.name}'); self.ui(self.status.set,f'Dokončeno | Ponecháno: {len(working)}'); self.ui(messagebox.showinfo,'Dokončeno',f'Výsledky jsou zde:\n{out}')
        except Exception as e:self.ui(messagebox.showerror,'Chyba',str(e)); self.ui(self.write,f'CHYBA: {e}')
        finally:self.running=False; self.ui(self.start_btn.config,state='normal'); self.ui(self.stop_btn.config,state='disabled')
if __name__=='__main__':App().mainloop()
