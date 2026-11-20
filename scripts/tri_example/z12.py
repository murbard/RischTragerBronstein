from fractions import Fraction as Fr
# Q(zeta12): basis 1,z,z^2,z^3 with z^4 = z^2 - 1
class Z:
    __slots__=('c',)
    def __init__(s,c=0):
        if isinstance(c,Z): s.c=c.c; return
        if isinstance(c,(list,tuple)): s.c=tuple(Fr(x) for x in c)+(Fr(0),)*(4-len(c))
        else: s.c=(Fr(c),Fr(0),Fr(0),Fr(0))
    @staticmethod
    def w(o): return o if isinstance(o,Z) else Z(o)
    def __add__(s,o): o=Z.w(o); return Z([a+b for a,b in zip(s.c,o.c)])
    __radd__=__add__
    def __neg__(s): return Z([-a for a in s.c])
    def __sub__(s,o): return s+(-Z.w(o))
    def __rsub__(s,o): return Z.w(o)-s
    def __mul__(s,o):
        o=Z.w(o); r=[Fr(0)]*7
        for i,a in enumerate(s.c):
            if a==0: continue
            for j,b in enumerate(o.c):
                if b: r[i+j]+=a*b
        for d in (6,5,4):   # z^d = z^(d-2) - z^(d-4)
            if r[d]: r[d-2]+=r[d]; r[d-4]-=r[d]; r[d]=Fr(0)
        return Z(r[:4])
    __rmul__=__mul__
    def iszero(s): return all(a==0 for a in s.c)
    def __eq__(s,o): return s.c==Z.w(o).c
    def __hash__(s): return hash(s.c)
    def inv(s):
        # solve s*x=1 : 4x4 linear system
        cols=[ (s*Z([1 if k==j else 0 for k in range(4)])).c for j in range(4)]
        M=[[cols[j][i] for j in range(4)]+[Fr(1 if i==0 else 0)] for i in range(4)]
        for c in range(4):
            piv=next(r for r in range(c,4) if M[r][c]!=0)
            M[c],M[piv]=M[piv],M[c]
            iv=1/M[c][c]; M[c]=[iv*x for x in M[c]]
            for r in range(4):
                if r!=c and M[r][c]!=0:
                    f=M[r][c]; M[r]=[x-f*y for x,y in zip(M[r],M[c])]
        return Z([M[i][4] for i in range(4)])
    def __truediv__(s,o): return s*Z.w(o).inv()
    def __rtruediv__(s,o): return Z.w(o)*s.inv()
    def __pow__(s,n):
        r=Z(1)
        for _ in range(n): r=r*s
        return r
    def lean(s):
        def f(x): return f"({x.numerator})" if x.denominator==1 else f"({x.numerator}/{x.denominator})"
        return "z "+" ".join(f(x) for x in s.c)
    def red(s,p,sp):
        v=0
        for k,a in enumerate(s.c):
            assert a.denominator%p!=0, ("denominator",p,s.c)
            v+=a.numerator*pow(a.denominator,-1,p)*pow(sp,k,p)
        return v%p
    def __repr__(s): return "Z"+str(tuple(str(x) for x in s.c))
zeta=Z([0,1]); I=zeta**3; W3=zeta**4   # W3 primitive cube root of unity
assert (I*I+1).iszero() and (W3*W3+W3+1).iszero()
