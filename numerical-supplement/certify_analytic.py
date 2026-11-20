"""Directed interval certificate for the asymmetric zeta(3) determinant.

Float root solvers only propose rational brackets. Every bracket is checked
with outward interval arithmetic before it is used. No quadrature error
estimate from a floating-point library enters the certificate.
"""
import argparse,json,time
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
import mpmath as mp

if not __debug__:
 raise RuntimeError('Run the certificate without Python optimization flags.')

iv=mp.iv
iv.dps=45

def rat_tuple(t):
 sign,man,exp,_=t
 return Q((-1 if sign else 1)*man)*(Q(2)**exp)
def lower(x):return rat_tuple(x._mpi_[0])
def upper(x):return rat_tuple(x._mpi_[1])
def I(x):
 if isinstance(x,Q):return iv.mpf(x.numerator)/x.denominator
 return iv.mpf(x)
def hull(a,b):return iv.mpf([I(a).a,I(b).b])
def out(x,places=12):
 scale=10**places
 a=lower(x)*scale;b=upper(x)*scale
 al=a.numerator//a.denominator
 bu=-((-b.numerator)//b.denominator)
 return {'lower':str(Q(al,scale)),'upper':str(Q(bu,scale)),
         'decimal_lower':al/scale,'decimal_upper':bu/scale}
def floor_rat(x,places=12):
 z=lower(x)*10**places
 return Q(z.numerator//z.denominator,10**places)
def ceil_rat(x,places=12):
 z=upper(x)*10**places
 return Q(-((-z.numerator)//z.denominator),10**places)

s1=Q(2,25);s2=Q(8,25);delta=Q(51,50);u=Q(1000001,1000000)
T=Q(17,125);Tcap=Q(7,50);lam=Q(17,25)
S1=I(s1);S2=I(s2);DE=I(delta);U=I(u)
log=iv.ln;sqrt=iv.sqrt

def mass(b):
 return (b+1-S1-S2-sqrt(1+b*b)+sqrt(S1*S1+b*b)+sqrt(S2*S2+b*b))/2
def mass_float(b):
 return (b+1-float(s1+s2)-np.hypot(1,b)+np.hypot(float(s1),b)+np.hypot(float(s2),b))/2

brackets_checked=0
max_bracket_width=Q(0)
def checked_root(fun,ffun,lo,hi,proposal=None):
 global brackets_checked,max_bracket_width
 x=brentq(ffun,lo,hi,xtol=1e-14) if proposal is None else proposal
 center=Q(str(x));step=Q(1,10**11)
 for _ in range(10):
  a=max(Q(0),center-step);b=center+step
  if upper(fun(I(a)))<0 and lower(fun(I(b)))>0:
   brackets_checked+=1;max_bracket_width=max(max_bracket_width,b-a)
   return hull(a,b)
  step*=10
 raise ArithmeticError(('Unverified root bracket',x))

def b_for(v):
 if v==0:return I(0)
 return checked_root(lambda b:mass(b)-I(v),lambda b:mass_float(b)-float(v),0,4)

def b_compressed(t):
 if t==0:return b_for(delta)
 return checked_root(lambda b:mass(b)+I(t)*U/sqrt(U*U+b*b)-DE,
                     lambda b:mass_float(b)+float(t*u)/np.hypot(float(u),b)-float(delta),0,4)

def analytic_integrand(v,b):
 if v==0:return 2*(S1+S2)*log(2)
 V=I(v)
 return sum(2*(S+V)*log(4*(S+V))-2*S*log(S+sqrt(S*S+b*b)) for S in (S1,S2))-4*V*log(b)+2*log((1+sqrt(1+b*b))/2)

def ineg(a):
 A=I(a)
 return A*log(U*U-A*A)+U*log((U+A)/(U-A))-2*A
BASE=ineg(s1)+ineg(s2)-ineg(Q(1))-2+sum(2*S*(1-log(S)) for S in (S1,S2))

def gamma_at_b(b):
 v=mass(b);uu=sqrt(U*U+b*b)
 def J(A):
  aa=sqrt(A*A+b*b)
  return log((uu+aa)/(U+A))-(A/U)*log((U*aa+A*uu)/(A*(uu+U)))
 return BASE+4*v*log((U+uu)/b)+2*U*(log((b+uu)/U)-J(I(1))+J(S1)+J(S2))

def green_H(b):
 x=b*b/(U*U)
 C=x/(2*(1+sqrt(1-x*x)))
 r=(1+sqrt(1-x))**2/x
 q=1/sqrt(1+x)
 return log(C)+q*log(r)


def main(args):
 start=time.time()
 result={'parameters':{k:str(v) for k,v in dict(s1=s1,s2=s2,delta=delta,u=u,T=T,Tcap=Tcap,degree_rate=lam).items()},
 'interval_decimal_precision':iv.dps,'method':'Directed interval arithmetic; checked rational root brackets; monotone Riemann sums; rational midpoint angular charges.'}
 b0=b_for(delta)
 assert upper(b0)<u and Tcap<min(delta,u/2)
 result['physical_support_endpoint']=out(b0)
 # g'(v)=2 log(16(s1+v)(s2+v)/b(v)^2)>0 because b(v)<=2v.
 # Consequently a left Riemann sum is a rigorous lower bound.
 n=args.analytic_panels;step=delta/n;total=I(0)
 for k in range(n):
  v=step*k;total+=analytic_integrand(v,b_for(v))
 can_lower=I(step)*total
 result['analytic_panels']=n;result['analytic_lower']=out(can_lower)
 print(json.dumps({'stage':'analytic','lower':out(can_lower)}),flush=True)
 # b^2/(u^2+b^2)^(3/2) increases for b<sqrt(2)u; b0<u suffices.
 n=args.linear_panels;step=(delta-Tcap)/n;total=I(0)
 for k in range(n):
  b=b_for(step*k)
  total+=U*b*b/((U*U+b*b)*sqrt(U*U+b*b))
 linear_integral=I(step)*total
 c=floor_rat(linear_integral,12);C=I(c)
 assert c>0
 result['linear_panels']=n;result['linear_coefficient']=str(c)
 result['linear_integral_lower']=out(linear_integral)
 print(json.dumps({'stage':'linear','coefficient':str(c)}),flush=True)
 # Midpoint Jensen lower sums: all nodes, weights and pole distances are rational.
 na=args.angular_panels;width=(1-s1-s2)/na;K=width/2
 nodes=[s1+s2+(Q(j)+Q(1,2))*width for j in range(na)]
 ee=[(u*u-x*x)**2/(2*u*u*x*x) for x in nodes]
 es=[I(e) for e in ee];IK=I(K)
 ef=np.array([float(e) for e in ee]);kf=float(K);cf=float(c)
 def amass(B):return C*B/2+sum(IK*(1-1/sqrt(1+B/e)) for e in es)
 def amassf(B):return cf*B/2+kf*np.sum(1-1/np.sqrt(1+B/ef))
 def angular_B(t):
  if t==0:return I(0)
  return checked_root(lambda B:amass(B)-I(t),lambda B:amassf(B)-float(t),0,1)
 def angular_F(t,B):
  if t==0:return I(0)
  return I(t)*log(B/2)-C*B/2-2*sum(IK*log((1+sqrt(1+B/e))/2) for e in es)
 Bcap=angular_B(Tcap)
 assert upper(Bcap)<1
 moment=C*Bcap*Bcap/8
 for e in es:
  S=sqrt(1+Bcap/e)
  moment+=IK*Bcap*(S-1)/(2*S*(S+1))
 Ap=-log(1-Bcap/2)/Bcap*moment/I(Tcap*Tcap)
 result['angular_panels']=na;result['angular_node_rule']='equally spaced rational midpoints on [s1+s2,1]'
 result['angular_charge_weight']=str(K);result['angular_endpoint_cap']=out(Bcap)
 result['physical_penalty']=out(Ap)
 # On each panel, b(t) decreases; F(t) decreases because B(t)<=1.
 # Every other expression is evaluated on the full enclosed b,t intervals.
 n=args.response_panels;step=T/n
 bleft=b_compressed(Q(0));Fleft=I(0)
 total_up=Q(0);total_low=Q(0);simple_up=Q(0);positive_lower=None
 for k in range(n):
  ta=k*step;tb=(k+1)*step
  bright=b_compressed(tb)
  bb=hull(lower(bright),upper(bleft));tt=I(hull(ta,tb))
  Fnew=angular_F(tb,angular_B(tb))
  FF=hull(lower(Fnew),upper(Fleft))
  gg=gamma_at_b(bb)+FF+2*tt*green_H(bb)+Ap*tt*tt
  total_up+=step*upper(gg);total_low+=step*lower(gg)
  positive_lower=lower(gg) if positive_lower is None else min(positive_lower,lower(gg))
  # Optional inherited estimate without the new global Green step.
  simple_gamma=gamma_at_b(b_for(delta-ta))
  simple_up+=step*(upper(simple_gamma)+upper(Fleft))
  bleft=bright;Fleft=Fnew
  if (k+1)%256==0:print(json.dumps({'stage':'response','completed':k+1,'panels':n}),flush=True)
 response=hull(total_low,total_up)
 result['response_panels']=n;result['response_integral']=out(response)
 result['response_integral_upper']=str(ceil_rat(response,12))
 result['simple_response_upper']=str(ceil_rat(I(simple_up),12))
 simple_endpoint=gamma_at_b(b_for(delta-T))+Fleft
 result['simple_envelope_at_T']=out(simple_endpoint)
 assert lower(simple_endpoint)>0
 result['envelope_positive_lower']=str(Q(positive_lower.numerator//positive_lower.denominator))
 assert positive_lower>0
 arith=json.loads(Path(args.arithmetic).read_text());car=Q(arith['arithmetic_upper'])
 can_cert=floor_rat(can_lower,12);response_cert=ceil_rat(response,12)
 gap=can_cert-car;margin=gap-response_cert
 result['arithmetic_upper']=str(car);result['analytic_certified_lower']=str(can_cert)
 result['gap_lower']=str(gap);result['decisive_margin_lower']=str(margin)
 result['decisive_margin_decimal']=float(margin)
 simple_margin=gap-ceil_rat(I(simple_up),12)
 result['simple_decisive_margin_lower']=str(simple_margin)
 result['simple_decisive_margin_decimal']=float(simple_margin)
 endpoint_upper=ceil_rat(simple_endpoint,12)
 measure_bound=lam*endpoint_upper/(simple_margin+T*endpoint_upper)
 result['transfer_bound_rational']=str(measure_bound)
 result['transfer_bound_decimal']=float(measure_bound)
 result['announced_measure_bound']='2487/500'
 assert measure_bound<Q(2487,500)
 result['verified_root_brackets']=brackets_checked;result['max_root_bracket_width']=str(max_bracket_width)
 result['integrated_envelope_target']=str(lam/T)
 result['main_envelope']='Gamma(delta-t)+F(t); no modified physical equilibrium or Green-function refinement required'
 result['passed']=bool(simple_margin>0 and lower(simple_endpoint)>0)
 result['wall_seconds']=time.time()-start
 Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2),flush=True)
 if not result['passed']:raise SystemExit('The target inequality was not certified.')

if __name__=='__main__':
 p=argparse.ArgumentParser()
 p.add_argument('--analytic-panels',type=int,default=8192)
 p.add_argument('--linear-panels',type=int,default=2048)
 p.add_argument('--angular-panels',type=int,default=128)
 p.add_argument('--response-panels',type=int,default=1024)
 p.add_argument('--arithmetic',default=str(Path(__file__).parent/'certificates/arithmetic_certificate.json'))
 p.add_argument('--output',default=str(Path(__file__).parent/'replayed/analytic_certificate.json'))
 main(p.parse_args())
