"""Exact finite rational checker/data generator for the complete second layer.

Its finite obligations mirror FullProfileCells.Cell.FullValid and CellsFit.  No
real-variable, valuation, determinant or limiting statement is accepted by
this script: those implications are the Lean theorems around the data.
"""
from fractions import Fraction as Q
from dataclasses import dataclass
from pathlib import Path
import hashlib, json

@dataclass(frozen=True)
class Aff:
    a: Q = Q(0)
    b: Q = Q(0)
    def __add__(self, other):
        other=aff(other); return Aff(self.a+other.a,self.b+other.b)
    __radd__=__add__
    def __neg__(self): return Aff(-self.a,-self.b)
    def __sub__(self, other): return self+-aff(other)
    def __rsub__(self, other): return aff(other)+-self
    def __mul__(self, other):
        other=Q(other); return Aff(self.a*other,self.b*other)
    __rmul__=__mul__
    def at(self, x): return self.a+self.b*x

def aff(v): return v if isinstance(v,Aff) else Aff(Q(v))
X=Aff(Q(0),Q(1))
class Split(Exception):
    def __init__(self, point): self.point=point
class Cell:
    def __init__(self,l,r): self.lo=l;self.hi=r;self.mid=(l+r)/2
    def minimum(self,x,y):
        x,y=aff(x),aff(y); z=x-y
        l,r=z.at(self.lo),z.at(self.hi)
        if l<=0 and r<=0:return x
        if l>=0 and r>=0:return y
        assert z.b
        cross=-z.a/z.b
        assert self.lo<cross<self.hi
        raise Split(cross)
    def maximum(self,x,y):return -self.minimum(-aff(x),-aff(y))

def floor(v): return v.numerator//v.denominator

def prefix(C,a,s,x):
    rem=s-a*X
    return 2*a*x+C.minimum(x,rem)+C.maximum(0,x+rem-X)

def shape(C,q,e,D,a,s,rho):
    w=1-(q+Q(e,2))*X
    roots=prefix(C,a,s,w) if e==0 else prefix(C,a,s,X*Q(1,2))-prefix(C,a,s,X*Q(1,2)-w)
    return D*w-roots+C.minimum(rho-Q(D,2)*X,w)

def numeric_cap(e,D1,D2,k1,k2,u1,u2):
    n1=max(0,D1+u1-k1);n2=max(0,D2+u2-k2)
    if e==0 and k1%2==0 and k2%2==0:
        return min((n1+1)//2,n2//2)+min(n1//2,(n2+1)//2)
    return min(n1,n2)

def expr(C,env,regime):
    q,e,d1,d2,a1,a2=env
    delta=Q(51,50)
    fac=Aff(d1*Q(11,10)+d2*Q(67,50)-2*delta*q,-Q(d1*(d1+1)+d2*(d2+1),4))
    terminal=C.maximum(0,Q(36,25)-X)
    if regime=='large':return fac+terminal
    A1=shape(C,q,e,d1,a1,Q(2,25),Q(11,10))
    A2=shape(C,q,e,d2,a2,Q(8,25),Q(67,50))
    first=(2+e)*delta+C.minimum(A1,A2)
    width=1-(q+Q(e,2))*X
    tlo=width if e==0 else aff(0)
    thi=X*Q(1,2) if e==0 else X*Q(1,2)-width
    def bounds(a,s,j):
        rem=s-a*X
        lower=rem if j==0 else aff(0) if j==1 else X-rem
        upper=C.minimum(rem,X-rem) if j==1 else X*Q(1,2)
        return lower,upper
    def length(i,j):
        l1,h1=bounds(a1,Q(2,25),i);l2,h2=bounds(a2,Q(8,25),j)
        return C.maximum(0,C.minimum(thi,C.minimum(h1,h2))-C.maximum(tlo,C.maximum(l1,l2)))
    def second(u1,u2):
        local=sum((numeric_cap(e,d1,d2,2*a1+i,2*a2+j,u1,u2)*length(i,j)
            for i in range(3) for j in range(3)),aff(0))
        K1=C.maximum(0,Q(11,10)-Q(d1,2)*X-width)
        K2=C.maximum(0,Q(67,50)-Q(d2,2)*X-width)
        return (1+e)*delta+A1+A2+local+(1-u1)*K1+(1-u2)*K2
    full=C.minimum(first,C.minimum(C.minimum(second(0,0),second(0,1)),C.minimum(second(1,0),second(1,1))))
    if regime=='middle':return full
    assert regime=='upper'
    saving=lambda s:C.minimum(s,1-X)+C.maximum(0,1+s-2*X)
    upper=fac+5*(1-X)-saving(Q(2,25))-saving(Q(8,25))+C.minimum(terminal,Q(1,50)+X)
    return C.minimum(full,upper)

def environment(mid):
    q=floor(1/mid);e=floor(2/mid)-2*q
    assert e in (0,1)
    return q,e,floor(Q(11,5)/mid),floor(Q(67,25)/mid),floor(Q(2,25)/mid),floor(Q(8,25)/mid)

def check_cell(l,r,env,regime,A):
    assert 0<l<r
    q,e,d1,d2,a1,a2=env
    for value,k in [(Q(1),q),(Q(11,5),d1),(Q(67,25),d2),(Q(2,25),a1),(Q(8,25),a2)]:
        assert k*r<=value<=(k+1)*l
    assert ((2*q+1)*r<=2) if e else (2<=(2*q+1)*l)
    assert (r<=1 if regime=='middle' else Q(16,25)<=l and r<=1 if regime=='upper' else 1<=l)
    assert expr(Cell(l,r),env,regime)==A

def lean_rat(q):
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'

def generate():
    lo,hi=Q(1,500),Q(67,25)
    base={lo,hi,Q(1),Q(2),Q(16,25)}
    for value in (Q(1),Q(2),Q(11,5),Q(67,25),Q(2,25),Q(8,25)):
        base.update(value/k for k in range(1,floor(value/lo)+1) if lo<=value/k<=hi)
    base=sorted(base);cells=[];scale=10**18
    for l,r in zip(base,base[1:]):
        stack=[(l,r)]
        while stack:
            l,r=stack.pop();C=Cell(l,r);env=environment(C.mid)
            regime='large' if C.mid>=1 else 'upper' if C.mid>Q(16,25) else 'middle'
            try:A=expr(C,env,regime)
            except Split as split:
                stack.extend([(split.point,r),(l,split.point)]);continue
            check_cell(l,r,env,regime,A)
            area=(r-l)*(A.a+A.b*(l+r)/2)
            rounded=-((-area.numerator*scale)//area.denominator)
            assert area<=Q(rounded,scale)
            cells.append((l,r,env,regime,A,rounded))
    assert cells[0][0]==lo and cells[-1][1]==hi
    assert all(a[1]==b[0] for a,b in zip(cells,cells[1:]))
    area=sum(((r-l)*(A.a+A.b*(l+r)/2) for l,r,_,_,A,_ in cells),Q(0))
    area_upper=Q(sum(row[-1] for row in cells),scale)
    tail=Q(51,6250);bound=area_upper+tail
    out=Path(__file__).parent
    rows=[];lean=['import Zeta3.Arithmetic.FullProfileCells','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
        '-- Generated by generate_full_cells.py using exact rational arithmetic.',
        '-- This file contains data only. Finite validation evidence is separate.',
        'namespace Zeta3.Arithmetic.ProfileCertificate','',
        'def fullCells : List Cell := [']
    for l,r,env,regime,A,rounded in cells:
        q,e,d1,d2,a1,a2=env
        rows.append('\t'.join(map(str,(l,r,q,e,d1,d2,a1,a2,regime,A.a,A.b,rounded))))
        lean.append(f'  ⟨{lean_rat(l)}, {lean_rat(r)}, ⟨{q}, {str(bool(e)).lower()}, {d1}, {d2}, {a1}, {a2}⟩, .{regime}, ⟨{lean_rat(A.a)}, {lean_rat(A.b)}⟩⟩,')
    lean[-1]=lean[-1].rstrip(',');lean+= [']','',f'def fullArithmeticUpper : ℚ := {lean_rat(bound)}','',
        'end Zeta3.Arithmetic.ProfileCertificate','']
    data='\n'.join(rows)+'\n';(out/'full-cells.tsv').write_text(data)
    (out/'FullCellsData.lean').write_text('\n'.join(lean))
    report={'checker':'exact rational Cell.Valid/adjacency/area replay','cell_count':len(cells),
        'lo':str(lo),'hi':str(hi),'area_exact':str(area),'area_upper':str(area_upper),'tail':str(tail),
        'arithmetic_upper':str(bound),'arithmetic_upper_decimal':float(bound),
        'tsv_sha256':hashlib.sha256(data.encode()).hexdigest(),'finite_checks_passed':True}
    (out/'full-cells-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':generate()
