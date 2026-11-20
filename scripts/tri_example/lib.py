from z12 import Z, Fr, I, W3, zeta
class _F: zero=Z(0); one=Z(1)
def use_field(zero,one): _F.zero=zero; _F.one=one
def ZE(): return _F.zero
def ON(): return _F.one
def isz(x): return x.iszero() if isinstance(x,Z) else x==0
# ---- CPoly ops mirroring Lean (lists low->high, no trimming)
def zero_like(x): return x-x
def add(p,q):
    if not p: return list(q)
    if not q: return list(p)
    r=[]
    n=max(len(p),len(q))
    for i in range(n):
        if i<len(p) and i<len(q): r.append(p[i]+q[i])
        elif i<len(p): r.append(p[i])
        else: r.append(q[i])
    return r
def smul(c,p): return [c*x for x in p]
def mul(p,q):
    if not p: return []
    if not q:
        # Lean: add (smul a []) (0 :: mul p q) -> recursion; mul (a::p) [] = add [] (0::mul p []) ...
        # mul [a] [] = add [] (0 :: mul [] []) = [0]; so length = len p
        return [zero_like(p[0])]*len(p) if len(p)>0 else []
    z0=zero_like(p[0]); r=[z0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        if isz(a): continue
        for j,b in enumerate(q):
            r[i+j]=r[i+j]+a*b
    return r
def mul_lean_len(p,q):
    # exact Lean length semantics: mul (a::p) q = add (smul a q) (0 :: mul p q)
    if not p: return 0
    return max(len(q), 1+mul_lean_len(p[1:],q))
def mulL(p,q):
    r=mul(p,q); L=mul_lean_len(p,q)
    if len(r)<L: r=r+[zero_like(p[0])]*(L-len(r))
    return r[:L]
def compC(mu,r):
    acc=[]
    for a in reversed(mu): acc=add([a],mulL(acc,r))
    return acc
def xPowC(N): return [ZE()]*N+[ON()]
def shiftC(a,N): return add([a if not isinstance(a,int) else ON()*a],xPowC(N))
def bivEval(W,s,Y):
    acc=[]
    for c in reversed(W): acc=add(compC(c,s),mulL(Y,acc))
    return acc
def addB(W,V):
    if not W: return list(V)
    if not V: return list(W)
    return [add(W[0],V[0])]+addB(W[1:],V[1:])
def derivYB(W):
    if not W: return []
    return addB(W[1:],[[]]+derivYB(W[1:]))
def ordC(P):
    for i,x in enumerate(P):
        if not isz(x): return i
    return len(P)
def getD(l,i,d): return l[i] if 0<=i<len(l) else d
def rootCheck(Fc,a,N,prec,y):
    D=bivEval(derivYB(Fc),shiftC(a,N),y); H=bivEval(Fc,shiftC(a,N),y)
    o=ordC(D)
    ok= o<prec and o<len(D) and all(isz(getD(H,i,ZE())) for i in range(o+prec))
    return ok,o
def sepCheck(ys,prec):
    for k in range(len(ys)):
        for l in range(len(ys)):
            if k==l: continue
            if not any(not (getD(ys[k],i,ZE())-getD(ys[l],i,ZE())).iszero() for i in range(prec)): return False
    return True
def certCheck(Fc,n,a,N,ys,prec):
    return N>0 and len(ys)==n and all(rootCheck(Fc,a,N,prec,y)[0] for y in ys) and sepCheck(ys,prec)
# ---- truncated series tools (python only)
def strunc(p,L): return (list(p)+[ZE()]*L)[:L]
def smulS(p,q,L):
    r=[ZE()]*L
    for i,a in enumerate(p[:L]):
        if isz(a): continue
        for j,b in enumerate(q[:L-i]):
            r[i+j]=r[i+j]+a*b
    return r
def sdiv(p,q,L):  # q[0]!=0
    iq=q[0].inv(); r=[ZE()]*L
    for m in range(L):
        acc=getD(p,m,ZE())
        for i in range(m):
            acc=acc-getD(q,m-i,ZE())*r[i]
        r[m]=acc*iq
    return r
def evalFS(Fc,a,N,y,L):
    # F(a+T^N, y) truncated to L
    s=shiftC(a,N)
    acc=[ZE()]*L
    for c in reversed(Fc):
        cs=strunc(compC(c,s),L)
        acc=[u+v for u,v in zip(cs,smulS(y,acc,L))]
    return acc
def newton(Fc,a,N,y,L,iters=12):
    FY=derivYB(Fc)
    y=strunc(y,L)
    for _ in range(iters):
        H=evalFS(Fc,a,N,y,L+8); D=evalFS(FY,a,N,y,L+8)
        d=ordC(D)
        assert ordC(H)>=d, (ordC(H),d)
        q=sdiv(H[d:],D[d:],L)
        y=[u-v for u,v in zip(y,q)]
        if all(isz(x) for x in q): break
    return y
