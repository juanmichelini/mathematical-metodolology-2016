import json,re,sys
sys.setrecursionlimit(10000)
import os
S=os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','results','third-round')
ents=json.load(open(S+"/kept.json"))
tok_re=re.compile(r"\\|->|\(|\)|\{|\}|;|[A-Za-z_][A-Za-z0-9_,.]*")
class P:
    def __init__(s,t): s.t=t; s.i=0
    def peek(s): return s.t[s.i] if s.i<len(s.t) else None
    def eat(s,x=None):
        v=s.t[s.i]; s.i+=1
        assert x is None or v==x,(x,v); return v
    def term(s):
        if s.peek()=="\\":
            s.eat(); v=s.eat(); s.eat("->"); return ("lam",v,s.term())
        return s.app()
    def app(s):
        a=[s.atom()]
        while s.peek() not in (None,")",";","}","->","of"): a.append(s.atom())
        r=a[0]
        for x in a[1:]: r=("app",r,x)
        return r
    def atom(s):
        p=s.peek()
        if p=="(":
            s.eat(); t=s.term(); s.eat(")"); return t
        if p=="case":
            s.eat(); sc=s.term(); s.eat("of"); s.eat("{"); br=[]
            while s.peek()!="}":
                con=s.eat(); vs=[]
                while s.peek()!="->": vs.append(s.eat())
                s.eat("->"); body=s.term(); s.eat(";"); br.append((con,vs,body))
            s.eat("}"); return ("case",sc,br)
        return ("var",s.eat())
def parse(s):
    p=P(tok_re.findall(s)); t=p.term(); assert p.i==len(p.t),(s,p.t[p.i:]); return t
env0={
 "C_,R.0":0, "C_,R.1":lambda n:n+1,
 "C_,a_R.0":(), "C_,a_R.1":lambda c:lambda d:(c,)+d,
 "f0":lambda x:lambda y:x+y,
 "f2":lambda x:lambda y:x+y,
 "f3":lambda x:tuple(reversed(x)),
 "f12":lambda x:lambda y:x*y,
 "f24":lambda c:lambda e:e*len(c),
}
def ev(t,env):
    k=t[0]
    if k=="var": return env[t[1]]
    if k=="app": return ev(t[1],env)(ev(t[2],env))
    if k=="lam": return lambda v:ev(t[2],{**env,t[1]:v})
    if k=="case":
        v=ev(t[1],env)
        for con,vs,body in t[2]:
            if con.startswith("C_,R."):
                if con.endswith(".0") and v==0: return ev(body,env)
                if con.endswith(".1") and v>0: return ev(body,{**env,vs[0]:v-1})
            else:
                if con.endswith(".0") and v==(): return ev(body,env)
                if con.endswith(".1") and len(v)>0: return ev(body,{**env,vs[0]:v[0],vs[1]:v[1:]})
        raise Exception("no branch")
def mk(e):
    t=parse(e["f"]); holder=[None]
    env2=dict(env0); env2["f"]=lambda x:holder[0](x)
    holder[0]=ev(t,env2); return holder[0]
def arg(kind,i): return i if kind=="C_,R" else tuple(range(1,i+1))
def show(v): return ("L"+str(list(v))) if isinstance(v,tuple) else str(v)
out={}
for e in ents:
    f=mk(e); argt=[x.strip() for x in e["t"].split("->")]
    grid={}
    for i in range(5):
        for j in range(4):
            grid[(i,j)]=f(arg(argt[0],i))(arg(argt[1],j))
    ig2=all(grid[(i,j)]==grid[(i,0)] for i in range(5) for j in range(4))
    ig1=all(grid[(i,j)]==grid[(0,j)] for i in range(5) for j in range(4))
    out[e["i"]]=(argt,grid,ig1,ig2)
    print(f"\n#{e['i']}  {argt[0]} -> {argt[1]} -> {argt[2]}   ignores 1st:{ig1} ignores 2nd:{ig2}")
    for i in range(5):
        cols=[0] if ig2 else range(3)
        print(f"   f({i}{'L' if argt[0]!='C_,R' else ''},{'*' if ig2 else 'j'}) =", " | ".join(show(grid[(i,j)]) for j in cols))
