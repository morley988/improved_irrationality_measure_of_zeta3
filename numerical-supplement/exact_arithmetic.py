"""Exact rational upper integration of the cubic two-window profile.
Each floor boundary is enumerated. Every min/max and ordering crossing is
split at its exact rational root, so accepted cells are affine throughout.
Cell areas are rounded UP to a fixed rational mesh. The small-prime tail
uses the proved bound 4*delta/Q, independently of any averaged tail.
"""
from fractions import Fraction as F
from dataclasses import dataclass
import hashlib,json,time,argparse

@dataclass(frozen=True)
class Aff:
 a:F=F(0)
 b:F=F(0)
 def __add__(self,y):
  y=aff(y);return Aff(self.a+y.a,self.b+y.b)
 __radd__=__add__
 def __neg__(self):return Aff(-self.a,-self.b)
 def __sub__(self,y):return self+-aff(y)
 def __rsub__(self,y):return aff(y)+-self
 def __mul__(self,y):
  if isinstance(y,Aff):
   assert not y.b or not self.b,'nonlinear multiplication'
   if not y.b:y=y.a
   else:return Aff(self.a*y.a,self.a*y.b)
  y=F(y);return Aff(self.a*y,self.b*y)
 __rmul__=__mul__
 def __truediv__(self,y):return self* (1/F(y))
 def at(self,x):return self.a+self.b*x

def aff(x):return x if isinstance(x,Aff) else Aff(F(x))
X=Aff(F(0),F(1))
class Split(Exception):
 def __init__(self,x):self.x=x
class Cell:
 def __init__(self,l,r):self.l=l;self.r=r;self.mid=(l+r)/2
 def le(self,x,y):
  z=aff(x)-aff(y);zl=z.at(self.l);zr=z.at(self.r)
  if zl<=0 and zr<=0:return True
  if zl>=0 and zr>=0:return False
  assert z.b
  cross=-z.a/z.b
  assert self.l<cross<self.r
  raise Split(cross)
 def amin(self,*xs):
  val=aff(xs[0])
  for x in xs[1:]:
   x=aff(x)
   if not self.le(val,x):val=x
  return val
 def amax(self,*xs):return -self.amin(*(-aff(x) for x in xs))
 def ordered(self,xs):
  ys=sorted(set(xs),key=lambda z:z.at(self.mid))
  for l,r in zip(ys,ys[1:]):assert self.le(l,r)
  return ys

def floor(x):return x.numerator//x.denominator

def profile(C,s1,s2,d):
 beta=C.mid;rhos=[s1+d,s2+d];ss=[s1,s2]
 q=floor(1/beta);ep=floor(2/beta)-2*q
 Ds=[floor(2*r/beta) for r in rhos];Hs=[r-D*X/2 for r,D in zip(rhos,Ds)]
 fac=sum((D*r-X*F(D*(D+1),4) for r,D in zip(rhos,Ds)),aff(0))-2*d*q
 terminal=C.amax(0,sum(rhos)-1-X)
 if beta>=1:return fac+terminal
 w=1-(q+F(ep,2))*X
 value=(2+ep)*d+C.amin(d,(min(Ds)+1)*w)
 # For the selected regime delta>1/2, each s_i<=D_i*beta/2 on beta<1.
 assert d>F(1,2)
 ml,mr=(aff(0),w) if ep==0 else (X/2-w,X/2)
 points=[aff(0),X/2,ml,mr];aa=[];rem=[];zbreak=[];rightk=[]
 for s in ss:
  a=floor(s/beta);rr=s-a*X;aa.append(a);rem.append(rr)
  zb=C.amin(rr,X-rr);zbreak.append(zb);points.append(zb)
  rightk.append(2*a if C.le(rr,X/2) else 2*a+2)
 pts=C.ordered(points);Ls=[aff(0),aff(0)];Bs=[[aff(0) for j in range(2)] for i in range(2)]
 for l,r in zip(pts,pts[1:]):
  z=(l+r)/2
  ks=[2*a+1 if C.le(z,zb) else kr for a,zb,kr in zip(aa,zbreak,rightk)]
  maximal=C.le(ml,z) and C.le(z,mr)
  if maximal:
   for i in range(2):Ls[i]+= (r-l)*max(0,Ds[i]-ks[i])
  else:
   for u1 in (0,1):
    for u2 in (0,1):
     n1=max(0,Ds[0]+u1-ks[0]);n2=max(0,Ds[1]+u2-ks[1]);cap=min(n1,n2)
     if ep==0 and ks[0]%2==0 and ks[1]%2==0:
      cap=min((n1+1)//2,n2//2)+min(n1//2,(n2+1)//2)
     Bs[u1][u2]+=(r-l)*cap
 As=[Li+C.amin(H,w) for Li,H in zip(Ls,Hs)];Ks=[C.amax(0,H-w) for H in Hs]
 for u1 in (0,1):
  for u2 in (0,1):Bs[u1][u2]+=(1-u1)*Ks[0]+(1-u2)*Ks[1]
 second=(1+ep)*d+sum(As,aff(0))+C.amin(*[b for row in Bs for b in row],d-As[0],d-As[1])
 value=C.amin(value,second)
 if beta>max(F(1,3),2*max(ss)) and d>=1-beta:
  roots=[aff(0) if beta<F(1,2) else C.amin(s,1-X)+C.amax(0,1+s-2*X) for s in ss]
  mono=fac+5*(1-X)-sum(roots,aff(0))+C.amin(terminal,d-1+X)
  value=C.amin(value,mono)
 return value

def run(s1,s2,d,Q=1000,scale=10**18,cell_file=None):
 assert F(0)<s1<=s2<F(1,2) and d>F(1,2)
 lo=F(1,Q);hi=max(2*(s2+d),F(1));base={lo,hi,F(1),F(1,2),F(1,3),2*s2,1-d}
 # These cover every floor used by profile. All other crossings are dynamic.
 for val in [F(1),F(2),s1,s2,2*s1,2*s2,2*(s1+d),2*(s2+d)]:
  for k in range(1,floor(val/lo)+1):
   pt=val/k
   if lo<=pt<=hi:base.add(pt)
 pts=sorted(p for p in base if lo<=p<=hi)
 total=0;count=0;splits=0;digest=hashlib.sha256();start=time.time();stream=open(cell_file,'w') if cell_file else None
 for l,r in zip(pts,pts[1:]):
  stack=[(l,r)]
  while stack:
   l,r=stack.pop();C=Cell(l,r)
   try:p=profile(C,s1,s2,d)
   except Split as e:
    splits+=1;stack.append((e.x,r));stack.append((l,e.x));continue
   area=(r-l)*(p.a+p.b*(l+r)/2)
   rounded=-((-area.numerator*scale)//area.denominator)
   assert F(rounded,scale)>=area
   total+=rounded;count+=1
   record=f'{l}\t{r}\t{p.a}\t{p.b}\t{rounded}\n';digest.update(record.encode())
   if stream:stream.write(record)
 if stream:stream.close()
 tail=4*d/Q;bound=F(total,scale)+tail
 return dict(s1=str(s1),s2=str(s2),delta=str(d),Q=Q,scale=scale,
 initial_cells=len(pts)-1,accepted_cells=count,dynamic_splits=splits,
 finite_area_upper=str(F(total,scale)),tail_upper=str(tail),arithmetic_upper=str(bound),
 arithmetic_upper_decimal=float(bound),rounding_error_upper=str(F(count,scale)),
 cell_sha256=digest.hexdigest(),wall_seconds=time.time()-start,
 notes='Exact floors and every min/max crossing; no numerical quadrature. Universal dimension/parity second layer only; no optional cubic exact-rank caps.')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--s1',default='1/5');ap.add_argument('--s2',default='1/5');ap.add_argument('--delta',default='51/50');ap.add_argument('--Q',type=int,default=1000);ap.add_argument('--output');ap.add_argument('--cells')
 ar=ap.parse_args();res=run(F(ar.s1),F(ar.s2),F(ar.delta),ar.Q,cell_file=ar.cells);out=json.dumps(res,indent=2);print(out)
 if ar.output:open(ar.output,'w').write(out+'\n')
