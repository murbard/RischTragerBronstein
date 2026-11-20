def make_gf(p):
    class GF:
        __slots__=('v',)
        P=p
        def __init__(s,v=0): s.v=(v.v if isinstance(v,GF) else int(v))%p
        @staticmethod
        def w(o): return o if isinstance(o,GF) else GF(o)
        def __add__(s,o): return GF(s.v+GF.w(o).v)
        __radd__=__add__
        def __neg__(s): return GF(-s.v)
        def __sub__(s,o): return GF(s.v-GF.w(o).v)
        def __rsub__(s,o): return GF(GF.w(o).v-s.v)
        def __mul__(s,o): return GF(s.v*GF.w(o).v)
        __rmul__=__mul__
        def inv(s): return GF(pow(s.v,-1,p))
        def __truediv__(s,o): return s*GF.w(o).inv()
        def iszero(s): return s.v==0
        def __eq__(s,o): return s.v==GF.w(o).v
        def __hash__(s): return hash(s.v)
        def __pow__(s,n): return GF(pow(s.v,n,p))
        def lean(s): return str(s.v)
        def __repr__(s): return f"{s.v}"
    return GF
