import sys,re,difflib,os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from cmp import dis,L,W
def norm(t):
    t=re.sub(r'@[0-9a-f]+','@X',t)
    t=re.sub(r'auipc\t(\w+),0x[0-9a-f]+',r'auipc \1,HI',t)
    t=re.sub(r'(-?\d+)\((\w+)\) # (SYM:\S+)',r'LO(\2) \3',t)
    t=re.sub(r',(-?\d+) # (SYM:\S+)',r',LO \2',t)
    t=re.sub(r'SYM:0x8005c6e0|SYM:0x8001ad20','SYM:av+16',t)
    return t
for f in sys.argv[1:]:
    _,_,a=dis(L,f); _,_,b=dis(W,f)
    a=[norm(x) for x in a]; b=[norm(x) for x in b]
    print('==',f)
    for l in difflib.unified_diff(b,a,'while','lua',n=2,lineterm=''): print(l)
