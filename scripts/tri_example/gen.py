import sys
from lib import *
import lib
from z12 import Z, I, W3, Fr
from gf import make_gf
n=3
Fc=[[Z(0),Z(-8),Z(-1)],[Z(0),Z(3)],[],[Z(1)]]
def reflectC(M,P,zero): return [getD(P,M-j,zero) for j in range(M+1)]
def invB(W,k,D,zero):
    return [reflectC(max(D-k*i,0) if D>=k*i else 0,c,zero) if True else None for i,c in enumerate(W)]
def invB_lean(W,k,D,zero):
    r=[]
    for i,c in enumerate(W):
        M=D-k*i if D>=k*i else 0
        r.append(reflectC(M,c,zero))
    return r
def neg_odd(y): return [(-x if i%2 else x) for i,x in enumerate(y)]
def trunc(y,L): return strunc(y,L)
LL=40
use_field(Z(0),Z(1))
# ---------------- branches over K
yr=newton(Fc,-16,2,[Z(-4),Z(1)],LL,60)           # ramified at -16 (x=-16+T^2)
yrm=neg_odd(yr)
yu2=newton(Fc,-16,2,[Z(8)],LL,60)                # unramified root in x=-16+T^2
yu1=newton(Fc,-16,1,[Z(8)],LL,60)                # unramified rep with x=-16+T
y4p=newton(Fc,-4,2,[Z(2),I],LL,60); y4m=neg_odd(y4p)
y4u=newton(Fc,-4,2,[Z(-4)],LL,60)
y0=[newton(Fc,0,3,[Z(0),2*w,-(w*w)/2],LL,60) for w in (Z(1),W3,W3*W3)]
y32=[newton(Fc,32,1,[v],LL,60) for v in (Z(8),Z(-4)+12*I,Z(-4)-12*I)]
FcInf2=invB_lean(Fc,2,6,Z(0))      # CurveProb model (k=2)
FcInf1=invB_lean(Fc,1,3,Z(0))      # integral-basis model (k=1)
LI=80
winf2=[newton(FcInf2,0,3,[Z(0)]*4+[w,-(w*w)],LI,120) for w in (Z(1),W3,W3*W3)]
winf1=[newton(FcInf1,0,3,[Z(0),w,-(w*w)],LL,60) for w in (Z(1),W3,W3*W3)]
def chk(name,Fc_,a,N,ys,prec):
    ok=certCheck(Fc_,n,Z.w(a) if not isinstance(a,Z) else a,N,ys,prec)
    print("cert",name,ok,[rootCheck(Fc_,Z.w(a) if not isinstance(a,Z) else a,N,prec,y)[1] for y in ys],file=sys.stderr)
    assert ok,name
    return ys
def cut(ys,m): return [trunc(y,m) for y in ys]
# CurveProb certs
PREC={0:8,-4:4,-16:6,32:3}
Ppts=[]
for a,N,ys in [(0,3,y0),(-4,2,[y4p,y4m,y4u]),(-16,2,[yr,yrm,yu2]),(32,1,y32)]:
    pr=PREC[a]; yc=cut(ys,pr+6)
    chk(f"P{a}",Fc,Z(a),N,yc,pr); Ppts.append((Z(a),N,yc,pr))
INFPREC=60
winf2c=cut(winf2,INFPREC+12)
chk("Pinf",FcInf2,Z(0),3,winf2c,INFPREC)
# integral basis certs
IBP=[]
for a,N,ys in [(0,3,y0),(-4,2,[y4p,y4m,y4u]),(-16,2,[yr,yrm,yu2])]:
    pr=6; yc=cut(ys,pr+6); chk(f"IB{a}",Fc,Z(a),N,yc,pr); IBP.append((Z(a),N,yc,pr))
IBINFPREC=5
winf1c=cut(winf1,IBINFPREC+6)
chk("IBinf",FcInf1,Z(0),3,winf1c,IBINFPREC)
# ---------------- place certificate
TP=[8,4]
places=[(0,2,trunc(yr,14),10),(0,1,trunc(yu1,10),6),(1,1,trunc(y32[0],10),6),(1,1,trunc(y32[1],10),6),(1,1,trunc(y32[2],10),6)]
fib=[(Z(-16),2),(Z(32),1)]
rt=[[(0,1,Z(1)),(0,1,Z(-1)),(1,2,Z(1))],[(2,1,Z(1)),(3,1,Z(1)),(4,1,Z(1))]]
Gp=[1,2,1,2,0]; cf=[2,2]; dG=[3,3]; cG=2
for (j,e,y,pp) in places:
    ok,o=rootCheck(Fc,fib[j][0],e,pp,y); print("place",j,e,ok,o,file=sys.stderr); assert ok
def conjC(zeta,s,y):
    return [ (zeta**m)*y[m//s] if m%s==0 else zeta-zeta for m in range(s*len(y))]
def apx(D_rt,D_pl,j,k):
    pi,s,zt=D_rt[j][k]; return conjC(zt,s,D_pl[pi][2])
for j in range(2):
    for k in range(3):
        for l in range(3):
            if k!=l:
                a1=apx(rt,places,j,k); a2=apx(rt,places,j,l)
                assert any(not (getD(a1,i,Z(0))-getD(a2,i,Z(0))).iszero() for i in range(TP[j])),(j,k,l)
# Γ arithmetic checks
for pi,(j,e,y,pp) in enumerate(places): assert Gp[pi]<=cf[j]*e
for j in range(2):
    assert sum(rt[j][k][1]*Gp[rt[j][k][0]] for k in range(3))==fib[j][1]*dG[j]
    assert dG[j]<=n*cf[j]
    for k in range(3):
        pi,s,zt=rt[j][k]; assert places[pi][0]==j and fib[j][1]==s*places[pi][1] and (zt**fib[j][1]-1).iszero() and TP[j]<=s*places[pi][3]
assert sum(dG)==cG*n
assert sum(cf[places[pi][0]]*places[pi][1]-Gp[pi] for pi in range(5))==sum(n*cf[j]-dG[j] for j in range(2))
# ---------------- test matrices
def test_matrix(fibv,rtv,plv,M,m,one,zero,delta=(0,1,2)):
    cols=[(i,d) for i in range(n) for d in range(M+1) if d+delta[i]<=M]
    rows=[]; ents=[]
    for j in range(2):
        a,N=fibv[j]
        for k in range(3):
            pi,s,zt=rtv[j][k]
            b=m*(s*Gp[pi])
            ap=conjC(zt,s,plv[pi][2]); ap=strunc(ap,TP[j])
            pw=[ [one]+[zero]*(TP[j]-1) ]
            for i in range(1,n): pw.append(smulS(pw[-1],ap,TP[j]))
            sh=shiftC(a,N)
            for t in range(b):
                row=[]
                for (i,d) in cols:
                    xd=[one]
                    for _ in range(d): xd=mulL(xd,sh)
                    prod=mulL(xd,pw[i])
                    row.append(getD(prod,t,zero))
                rows.append((j,k,t)); ents.append(row)
    return cols,rows,ents
def solve_left_inverse(A,one,zero):
    R=len(A); C=len(A[0])
    # pick independent rows greedily
    basis=[]; sel=[]
    def rank_add(vecs):
        M=[v[:] for v in vecs]; r=0
        for c in range(C):
            piv=next((i for i in range(r,len(M)) if not M[i][c].iszero()),None)
            if piv is None: continue
            M[r],M[piv]=M[piv],M[r]; iv=M[r][c].inv(); M[r]=[iv*x for x in M[r]]
            for i in range(len(M)):
                if i!=r and not M[i][c].iszero():
                    f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
            r+=1
        return r
    for ri in range(R):
        if rank_add([A[x] for x in sel]+[A[ri]])>len(sel): sel.append(ri)
        if len(sel)==C: break
    assert len(sel)==C, ("rank",len(sel),C)
    S=[A[r] for r in sel]   # C x C ; want L S = I  -> L = S^{-1}
    Mx=[S[t][:]+[one if t==u else zero for u in range(C)] for t in range(C)]
    # we need X with X*S = I ; compute inverse of S (S^{-1} S = I)
    for c in range(C):
        piv=next(r for r in range(c,C) if not Mx[r][c].iszero())
        Mx[c],Mx[piv]=Mx[piv],Mx[c]; iv=Mx[c][c].inv(); Mx[c]=[iv*x for x in Mx[c]]
        for r in range(C):
            if r!=c and not Mx[r][c].iszero():
                f=Mx[r][c]; Mx[r]=[x-f*y for x,y in zip(Mx[r],Mx[c])]
    Sinv=[row[C:] for row in Mx]
    return sel,Sinv
def kernel_vec(A,one,zero):
    rows=len(A); cols=len(A[0])
    Mx=[r[:] for r in A]; pivc=[]; r=0
    for c in range(cols):
        piv=next((i for i in range(r,rows) if not Mx[i][c].iszero()),None)
        if piv is None: continue
        Mx[r],Mx[piv]=Mx[piv],Mx[r]; iv=Mx[r][c].inv(); Mx[r]=[iv*x for x in Mx[r]]
        for i in range(rows):
            if i!=r and not Mx[i][c].iszero():
                f=Mx[i][c]; Mx[i]=[x-f*y for x,y in zip(Mx[i],Mx[r])]
        pivc.append(c); r+=1
        if r==rows: break
    free=[c for c in range(cols) if c not in pivc]
    if not free: return None
    fc=free[0]; v=[zero]*cols; v[fc]=one
    for i,c in enumerate(pivc): v[c]=zero-Mx[i][fc]
    return v
MP={13:1,109:2}; MM=MP[13]*MP[109]
M_C=MM*cG
cols,rows,A=test_matrix(fib,rt,places,M_C,MM,Z(1),Z(0))
print("C test",len(rows),"x",len(cols),file=sys.stderr)
sel,Sinv=solve_left_inverse(A,Z(1),Z(0))
Pb=8
LmC={}
for ci,(i,d) in enumerate(cols):
    row=[Z(0)]*(2*n*Pb)
    for si,r in enumerate(sel):
        j,k,t=rows[r]; row[(j*n+k)*Pb+t]=Sinv[ci][si]
    LmC[i*(M_C+1)+d]=row
# verify
for ci,(i,d) in enumerate(cols):
    for cj in range(len(cols)):
        s_=Z(0)
        for r,(j,k,t) in enumerate(rows): s_=s_+LmC[i*(M_C+1)+d][(j*n+k)*Pb+t]*A[r][cj]
        assert s_==(Z(1) if ci==cj else Z(0))
print("LmC ok",file=sys.stderr)
# ---------------- primes
def red_root(p):
    for s in range(p):
        if (s**4-s*s+1)%p==0 and (4*s**3-2*s)%p!=0: return s
PR={}
for p in (13,109):
    sp=red_root(p); GF=make_gf(p); o,z=GF(1),GF(0)
    R=lambda x: GF(x.red(p,sp))
    use_field(z,o)
    Fp=[[R(c) for c in col] for col in Fc]
    FpI=invB_lean(Fp,1,3,z)
    # IB certs mod p
    ppts=[]
    for (a,N,ys,pr) in IBP:
        yp=[[R(c) for c in y] for y in ys]
        assert certCheck(Fp,n,R(a),N,yp,pr), ("IBcert mod",p,a)
        # matEntry: coeff r%N of y_{r/N}^j
        Mt=[[ (lambda y: getD([o] if j==0 else (y if j==1 else mulL(y,y)),r%N,z))(yp[r//N]) for j in range(n)] for r in range(n*N)]
        # left inverse n x (nN): L M = I
        Mt_T=Mt
        sel2,Sinv2=solve_left_inverse(Mt,o,z)
        Lm=[[z]*(n*N) for _ in range(n)]
        for ci in range(n):
            for si,r in enumerate(sel2): Lm[ci][r]=Sinv2[ci][si]
        ppts.append((R(a),N,yp,pr,Lm))
    wp=[[R(c) for c in y] for y in winf1c]
    assert certCheck(FpI,n,z,3,wp,IBINFPREC)
    Mt=[[getD([o] if j==0 else (wp[r//3] if j==1 else mulL(wp[r//3],wp[r//3])),r%3,z) for j in range(n)] for r in range(9)]
    sel2,Sinv2=solve_left_inverse(Mt,o,z)
    Linf=[[z]*9 for _ in range(n)]
    for ci in range(n):
        for si,r in enumerate(sel2): Linf[ci][r]=Sinv2[ci][si]
    # base point
    def evB(W,a,b):
        acc=z
        for c in reversed(W):
            ca=z
            for cc in reversed(c): ca=cc+a*ca
            acc=ca+b*acc
        return acc
    bad={R(Z(0)).v,R(Z(-4)).v,R(Z(-16)).v,R(Z(32)).v}
    x1=None
    for xv in range(1,p):
        if xv in bad: continue
        rts=[yv for yv in range(p) if evB(Fp,GF(xv),GF(yv)).iszero()]
        if len(rts)==3: x1=GF(xv); ys1=[GF(v) for v in rts]; break
    y0_,y1_,y2_=ys1
    # lam: l1 + l2 = 1 ; l1 y1 + l2 y2 = y0
    l2=(y0_-y1_)/(y2_-y1_); l1=o-l2
    lam=[[z,l1,l2]]
    V=[[o,y,y*y] for y in ys1]
    Linv=[[z]*3 for _ in range(3)]
    sel3,S3=solve_left_inverse(V,o,z)
    for ci in range(3):
        for si,r in enumerate(sel3): Linv[ci][r]=S3[ci][si]
    aI=None
    for av in range(p):
        if all(not evB(Fp,GF(av),GF(yv)).iszero() for yv in range(p)): aI=GF(av); break
    assert aI is not None
    # place prime data: witness
    mp=MP[p]
    fibp=[(R(a),N) for (a,N) in fib]
    rtp=[[(pi,s,R(zt)) for (pi,s,zt) in rj] for rj in rt]
    plp=[(j,e,[R(c) for c in y],pp) for (j,e,y,pp) in places]
    colsp,rowsp,Ap=test_matrix(fibp,rtp,plp,mp*cG,mp,o,z)
    v=kernel_vec(Ap,o,z); assert v is not None, ("no witness",p)
    Gw=[[z]*(mp*cG+1) for _ in range(n)]
    for (i,d),x in zip(colsp,v): Gw[i][d]=x
    # unit conditions
    for (j,e,y,pp) in places:
        a=fib[j][0]
        use_field(Z(0),Z(1)); Dg=bivEval(derivYB(Fc),shiftC(a,e),y); og=ordC(Dg)
        use_field(z,o); Dr=bivEval(derivYB(Fp),shiftC(R(a),e),[R(c) for c in y])
        assert not getD(Dr,og,z).iszero(), ("unit",p,j,e)
    # separation mod p
    for j in range(2):
        for k in range(3):
            for l in range(3):
                if k!=l:
                    a1=apx(rtp,plp,j,k); a2=apx(rtp,plp,j,l)
                    assert any(not (getD(a1,i,z)-getD(a2,i,z)).iszero() for i in range(TP[j])),("sepmod",p,j,k,l)
    PR[p]=dict(ppts=ppts,wp=wp,Linf=Linf,x1=x1,ys1=ys1,lam=lam,Linv=Linv,aI=aI,Gw=Gw,mp=mp)
    print("prime",p,"ok x1",x1,ys1,"aI",aI,file=sys.stderr)
use_field(Z(0),Z(1))
# ---------------- output
def L(x): return x.lean()
def lst(v): return "["+", ".join(L(x) for x in v)+"]"
def lst2(v): return "["+", ".join(lst(r) for r in v)+"]"
def cert(N,ys,pr): return f"⟨{N}, {lst2(ys)}, {pr}⟩"
out=[]
out.append("def FcT : BPoly QZ := "+lst2(Fc))
A1=[Fr(4,3)-4*I, Fr(1,12)+I/8]
A1=[Z(Fr(4,3))-4*I, Z(Fr(1,12))+I/8]
out.append("def probZ : CurveProb QZ :=\n  { Fc := FcT, n := 3, k := 2, A := [[], "+lst(A1)+"],\n    D := "+lst([Z(-512),Z(-16),Z(1)])+",\n    pts := ["+",\n      ".join(f"({L(a)}, {cert(N,ys,pr)})" for (a,N,ys,pr) in Ppts)+"],\n    inf := "+cert(3,winf2c,INFPREC)+" }")
out.append("def IBZ : IntBasisCert QZ :=\n  ⟨[[[z 1 0 0 0]], [[], [z 1 0 0 0]], [[], [], [z 1 0 0 0]]], [z 1 0 0 0], [0, 1, 2],\n   ["+",\n    ".join(f"({L(a)}, {cert(N,ys,pr)}, {lst2(Lm_)})" for (a,N,ys,pr),Lm_ in zip(IBP,[None]*3) for _ in [0] if False)+"]"
    if False else "")
# IB pts over K need Lm over K
IBout=[]
for (a,N,ys,pr) in IBP:
    Mt=[[getD([Z(1)] if j==0 else (ys[r//N] if j==1 else mulL(ys[r//N],ys[r//N])),r%N,Z(0)) for j in range(n)] for r in range(n*N)]
    sel2,Sinv2=solve_left_inverse(Mt,Z(1),Z(0))
    Lm=[[Z(0)]*(n*N) for _ in range(n)]
    for ci in range(n):
        for si,r in enumerate(sel2): Lm[ci][r]=Sinv2[ci][si]
    IBout.append(f"({L(a)}, {cert(N,ys,pr)}, {lst2(Lm)})")
Mt=[[getD([Z(1)] if j==0 else (winf1c[r//3] if j==1 else mulL(winf1c[r//3],winf1c[r//3])),r%3,Z(0)) for j in range(n)] for r in range(9)]
sel2,Sinv2=solve_left_inverse(Mt,Z(1),Z(0))
LinfK=[[Z(0)]*9 for _ in range(n)]
for ci in range(n):
    for si,r in enumerate(sel2): LinfK[ci][r]=Sinv2[ci][si]
out[-1]=("def IBZ : IntBasisCert QZ :=\n  ⟨[[[z 1 0 0 0]], [[], [z 1 0 0 0]], [[], [], [z 1 0 0 0]]], [z 1 0 0 0], [0, 1, 2],\n   ["
  +",\n    ".join(IBout)+"],\n   "+cert(3,winf1c,IBINFPREC)+", "+lst2(LinfK)+"⟩")
out.append("def TZ : GlobalCert QZ := ⟨FcT, 3, 1, 2, IBZ, z 0 0 0 0, [], [], [], [], 0⟩")
plstr=", ".join(f"({j}, {e}, {lst(y)}, {pp})" for (j,e,y,pp) in places)
rtstr="["+", ".join("["+", ".join(f"({pi}, {s}, {L(zt)})" for (pi,s,zt) in rj)+"]" for rj in rt)+"]"
out.append(f"def PcZ : PlaceCert QZ :=\n  ⟨[({L(fib[0][0])}, 2), ({L(fib[1][0])}, 1)],\n   [{plstr}],\n   {rtstr},\n   {Gp}, {cf}, {dG}, {cG}, {TP}⟩")
for p in (13,109):
    d=PR[p]
    ptsS=",\n    ".join(f"({a.v}, {cert(N,ys,pr)}, {lst2(Lm_)})" for (a,N,ys,pr,Lm_) in d['ppts'])
    out.append(f"def P{p} : PrimeCert {p} :=\n  ⟨[{ptsS}],\n   {cert(3,d['wp'],IBINFPREC)}, {lst2(d['Linf'])},\n   [{d['x1'].v}], [{lst(d['ys1'])}], {lst2(d['lam'])}, [{lst2(d['Linv'])}], [], 1, [[1]], some {d['aI'].v}⟩")
    out.append(f"def Q{p} : PlaceCert.PrimeData {p} := ⟨{d['mp']}, {lst2(d['Gw'])}⟩")
LmRows=[LmC.get(r,[]) for r in range(max(LmC)+1)]
out.append("def LmZ : List (List QZ) := "+lst2(LmRows))
out.append(f"def PbZ : ℕ := {Pb}")
print("\n\n".join(out))
