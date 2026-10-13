import subprocess,re,sys
T='/data/home/kirancodes/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-'
L='/data/home/kirancodes/Documents/code/ship-your-lua/c/lua-riscv-htif.elf'
W='/data/home/kirancodes/Documents/code/syi/c/while-riscv-htif.elf'
def syms(e):
    d={};sz={}
    for l in subprocess.run([T+'nm','-S','-n',e],capture_output=True,text=True).stdout.splitlines():
        p=l.split()
        if len(p)==4: d.setdefault(p[3],int(p[0],16)); sz.setdefault(p[3],int(p[1],16))
        elif len(p)==3: d.setdefault(p[2],int(p[0],16))
    return d,sz
SY={}
def dis(e,name):
    if e not in SY: SY[e]=syms(e)
    d,sz=SY[e]; a=d[name]; n=sz.get(name)
    out=subprocess.run([T+'objdump','-d','--no-show-raw-insn',f'--start-address={a}',f'--stop-address={a+n}',e],capture_output=True,text=True).stdout
    ins=[]
    inv={}
    for k,v in d.items(): inv.setdefault(v,k)
    for l in out.splitlines():
        m=re.match(r'^\s*([0-9a-f]+):\s+(.*)$',l)
        if m:
            t=m.group(2)
            t=re.sub(r'<[^>]*>','',t)
            def rel(mm):
                v=int(mm.group(0),16)
                if a<=v<a+n: return f'@{v-a:x}'
                return 'SYM:'+inv.get(v,hex(v))
            t=re.sub(r'\b8[0-9a-f]{7}\b',rel,t)
            ins.append(t.strip())
    return a,n,ins
if __name__=='__main__':
    for f in sys.argv[1:]:
        al,nl,il=dis(L,f); aw,nw,iw=dis(W,f)
        diff=[(i,x,y) for i,(x,y) in enumerate(zip(il,iw)) if x!=y]
        print(f, hex(al),nl, hex(aw),nw, 'len', len(il),len(iw),'diffs',len(diff))
        for dd in diff[:20]: print('  ',dd)
