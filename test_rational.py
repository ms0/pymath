# NOTE: this includes a test for rational.__pow__ as used in sha2.py
# NOTE: test_matrix.py also tests rational.py functionality
# NOTE: test_poly.py also tests rational.py functionality

import sys

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

else :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

  xrange = range;

from random import Random
from rational import *

R=Random();
randint=R.randint;
random=R.random;
R.seed(0);    # for test reproducibility

def ceq(c,v=()) :
  if not eval(c) : print(c,v);

def roottest(numbers=None,roots=(2,3),nbits=(32,64)) :
  if not numbers :
    from sha2 import P
    numbers = P;
  iroot = lambda x,r,b: int(rational(x<<(r*b))**rational(1,r));
  ipow = lambda x,r,b: (x**r)>>(r*b);
  for n in numbers :
    for r in roots :
      for b in nbits :
        x = iroot(n,r,b);
        xr = ipow(x,r,b);
        if xr != n :
          if xr >= n :
            print('%d root of %d overestimated for nbits=%d'%(r,n,b));
            break;
          if ipow(x+1,r,b) != n :
            print('%d root of %d underestimated for nbits=%d'%(r,n,b));
            break;

def testops(v) :    # v is vector of 3 values to be tested
  ceq('v[0]-v[0] == 0',v[:1])
  ceq('v[0]+-v[0] == 0',v[:1])
  ceq('not v[0] or v[0]/v[0] == 1',v[:1])
  ceq('not v[0] or v[0]*v[0]**-1 == 1',v[:1])
  ceq('not v[0] or 1/v[0] == v[0]**-1',v[:1])
  ceq('0*v[0] == 0',v[:1])
  ceq('1*v[0] == v[0]',v[:1])
  ceq('-1*v[0] == -v[0]',v[:1])
  ceq('v[0]+v[1] == v[1]+v[0]',v[:2])
  ceq('v[0]*v[1] == v[1]*v[0]',v[:2])
  ceq('not v[1] or v[0]/v[1]*v[1] == v[0]',v[:2])
  ceq('v[0]-v[1]+v[1] == v[0]',v[:2])
  ceq('(v[0]+v[1])+v[2] == v[0]+(v[1]+v[2])',v)
  ceq('(v[0]*v[1])*v[2] == v[0]*(v[1]*v[2])',v)
  ceq('v[0]*(v[1]+v[2]) == v[0]*v[1]+v[0]*v[2]',v)
  ceq('(v[0]+v[1])*v[2] == v[0]*v[2]+v[1]*v[2]',v)
  if isinstance(v[0],xrational) :
    ceq('not v[0] or abs(((v[0]*~v[0])-abs(v[0])**2)/(v[0]*~v[0]))<<set_significance() < 1',v[:1])

def ratspectest() :
  p0 = rational();
  m0 = -p0;
  pinf = rational(1,0);
  minf = -pinf;
  nan = rational(0,0);
  half = rational(1,2);
  ceq('v[0]!=v[0]',(nan,));
  for x in (p0,m0,pinf,minf) :
    ceq('v[0]==v[0]',(x,));
  ceq('v[0]==v[1]',(p0,m0));         # +0 == -0
  ceq('v[0]!=v[1]',(pinf,minf));     # +inf != -inf
  ceq('v[0]>v[1]',(pinf,minf));      # +inf > -inf
  ceq('v[0]>1>v[1]',(pinf,minf));    # +inf > 1 > -inf
  ceq('v[0]>v[2]>v[1]',(pinf,minf,p0));    # +inf > +0 > -inf
  ceq('v[0]>v[2]>v[1]',(pinf,minf,m0));    # +inf > -0 > -inf
  ceq('v[0]>v[2]>=v[3]>v[1]',(pinf,minf,p0,m0));    # +inf > +0 >= -0 > -inf
  ceq('v[0]>v[3]>=v[2]>v[1]',(pinf,minf,p0,m0));    # +inf > -0 >= +0 > -inf
  ceq('v[1]<v[0]',(pinf,minf));      # -inf < +inf
  ceq('v[1]<1<v[0]',(pinf,minf));    # -inf < 1 < +inf
  ceq('v[1]<v[2]<v[0]',(pinf,minf,p0));    # -inf < +0 < +inf
  ceq('v[1]<v[2]<v[0]',(pinf,minf,m0));    # -inf < -0 < +inf
  ceq('v[0]>v[2]>=v[3]>v[1]',(pinf,minf,p0,m0));    # +inf > +0 >= -0 > -inf
  ceq('v[0]>v[3]>=v[2]>v[1]',(pinf,minf,p0,m0));    # +inf > -0 >= +0 > -inf
  ceq('v[1]<v[2]<=v[3]<v[0]',(pinf,minf,p0,m0));    # -inf < +0 <= -0 > +inf
  ceq('v[1]<v[3]<=v[2]<v[0]',(pinf,minf,p0,m0));    # -inf < -0 <= +0 > +inf
  ceq('v[0] is 1/v[1]',(p0,pinf));   # +0 is 1/+inf
  ceq('v[0] is 1/v[1]',(m0,minf));   # -0 is 1/-inf
  ceq('v[0] is -1/v[1]',(p0,minf));  # +0 is -1/-inf
  ceq('v[0] is -1/v[1]',(m0,pinf));  # -0 is -1/+inf
  ceq('v[1] is 1/v[0]',(p0,pinf));   # +inf is 1/+0
  ceq('v[1] is 1/v[0]',(m0,minf));   # -inf is 1/-0
  ceq('v[1] is -1/v[0]',(p0,minf));  # -inf is -1/+0
  ceq('v[1] is -1/v[0]',(m0,pinf));  # +inf is -1/-0
  ceq('v[0] is v[0]/v[1]',(p0,pinf));# +0 is +0/+inf
  ceq('v[0] is v[0]/v[1]',(m0,pinf));# -0 is -0/+inf
  ceq('-v[0] is v[0]/v[1]',(p0,minf)); # -+0 is +0/-inf
  ceq('-v[0] is v[0]/v[1]',(m0,minf)); # --0 is -0/-inf
  ceq('v[1] is v[1]/v[0]',(p0,pinf));# +inf is +inf/+0
  ceq('v[1] is v[1]/v[0]',(p0,minf));# -inf is -inf/+0
  ceq('-v[1] is v[1]/v[0]',(m0,pinf)); # -+inf is -0/+inf
  ceq('-v[1] is v[1]/v[0]',(m0,minf)); # --inf is -0/-inf
  ceq('v[0] is not v[1]',(p0,m0));   # +0 is not -0
  ceq('v[0] is v[0]+v[0]',(p0,));    # +0 is +0 + +0
  ceq('v[0] is v[0]+v[0]',(m0,));    # -0 is -0 + -0
  ceq('v[0] is v[1]+v[0]',(p0,m0));  # +0 is -0 + +0
  ceq('v[0] is v[0]-v[0]',(p0,));    # +0 is +0 - +0
  ceq('v[0] is v[0]-v[1]',(p0,m0));  # +0 is +0 - -0
  ceq('v[0] is v[1]-v[1]',(p0,m0));  # +0 is -0 - -0
  ceq('v[1] is v[1]-v[0]',(p0,m0));  # -0 is -0 - +0
  ceq('v[0] is v[0]*v[0]',(p0,));    # +0 is +0 * +0
  ceq('v[0] is v[1]*v[1]',(p0,m0));  # +0 is -0 * -0
  ceq('v[1] is v[0]*v[1]',(p0,m0));  # -0 is +0 * -0
  ceq('v[1] is v[1]*v[0]',(p0,m0));  # -0 is -0 * +0
  ceq('v[0] is v[0]**v[1]',(p0,half));  # +0 is (+0)**.5
  ceq('v[0] is v[0]**v[1]',(m0,half));  # -0 is (-0)**.5
  ceq('v[0] is v[0]**v[1]',(p0,1));  # +0 is (+0)**1
  ceq('v[0] is v[0]**v[1]',(m0,1));  # -0 is (-0)**1
  ceq('v[0]**0 == 1',(p0,));         # (+0)**0 == 1
  ceq('v[0]**0 == 1',(m0,));         # (-0)**0 == 1    
  ceq('v[0]<<1 is v[0]',(p0,));      # (+0)<<1 == +0
  ceq('v[0]<<1 is v[0]',(m0,));      # (-0)<<1 == -0
  ceq('v[0]>>1 is v[0]',(p0,));      # (+0)>>1 == +0
  ceq('v[0]>>1 is v[0]',(m0,));      # (-0)>>1 == -0
  ceq('v[0] is -v[1]',(p0,m0));      # +0 is --0
  ceq('v[1] is -v[0]',(p0,m0));      # -0 is -+0
  ceq('v[0] is abs(v[0])',(p0,));    # +0 is abs(+0)
  ceq('v[0] is abs(v[1])',(p0,m0));  # +0 is abs(-0)
  ceq('v[0] is -v[1]',(pinf,minf));  # +inf is --inf
  ceq('v[1] is -v[0]',(pinf,minf));  # -inf is -+inf
  ceq('v[0] is abs(v[0])',(pinf,));    # +inf is abs(+inf)
  ceq('v[0] is abs(v[1])',(pinf,minf));  # +inf is abs(-inf)
  ceq('v[0] is v[1]/v[1]',(nan,p0));  # nan is +0/+0
  ceq('v[0] is v[1]/v[1]',(nan,m0));  # nan is -0/-0
  ceq('v[0] is v[1]/v[2]',(nan,p0,m0));  # nan is +0/-0
  ceq('v[0] is v[2]/v[1]',(nan,p0,m0));  # nan is -0/+0
  ceq('v[0] is v[1]/v[1]',(nan,pinf));  # nan is +inf/+inf
  ceq('v[0] is v[1]/v[1]',(nan,minf));  # nan is -inf/-inf
  ceq('v[0] is v[1]/v[2]',(nan,pinf,minf));  # nan is +inf/-inf
  ceq('v[0] is v[2]/v[1]',(nan,pinf,minf));  # nan is -inf/+inf
  ceq('v[0] is v[1]*v[2]',(nan,p0,pinf));  # nan is +0*+inf
  ceq('v[0] is v[2]*v[1]',(nan,p0,pinf));  # nan is +inf*+0
  ceq('v[0] is v[1]*v[2]',(nan,m0,minf));  # nan is -0*-inf
  ceq('v[0] is v[2]*v[1]',(nan,m0,minf));  # nan is -inf*-0
  ceq('v[0] is v[1]+v[2]',(nan,pinf,minf));  # nan is +inf+-inf  
  ceq('v[0] is v[2]+v[1]',(nan,pinf,minf));  # nan is -inf++inf
  ceq('v[0] == v[0]+v[1]',(1,p0));   # 1 == 1++0
  ceq('v[0] == v[0]+v[1]',(1,m0));   # 1 == 1+-0
  ceq('v[0] == v[0]+v[1]',(pinf,1)); # +inf == +inf+1
  ceq('v[0] == v[0]+v[1]',(minf,1)); # -inf == -inf+1
  ceq('v[0] == v[0]*v[1]',(pinf,2)); # +inf == +inf*2
  ceq('v[0] == v[0]*v[1]',(minf,2)); # -inf == -inf*2
  ceq('v[0] == v[1]*v[2]',(pinf,minf,-2));  # +inf == -inf*-2
  ceq('v[1] == v[0]*v[2]',(pinf,minf,-2));  # -inf == +inf*-2
  for x in (69,p0,m0,pinf,minf,nan) :
    ceq('v[0] != v[1]',(nan,x));
    ceq('v[1] != v[0]',(nan,x));
    ceq('not v[0] < v[1]',(nan,x));
    ceq('not v[1] < v[0]',(nan,x));
    ceq('not v[0] <= v[1]',(nan,x));
    ceq('not v[1] <= v[0]',(nan,x));
    ceq('not v[0] == v[1]',(nan,x));
    ceq('not v[1] == v[0]',(nan,x));
    ceq('not v[0] >= v[1]',(nan,x));
    ceq('not v[1] >= v[0]',(nan,x));
    ceq('not v[0] > v[1]',(nan,x));
    ceq('not v[1] > v[0]',(nan,x));
    ceq('v[0] is v[0]+v[1]',(nan,x));
    ceq('v[0] is v[0]-v[1]',(nan,x));
    ceq('v[0] is v[0]*v[1]',(nan,x));
    ceq('v[0] is v[0]/v[1]',(nan,x));
    ceq('v[0] is v[1]+v[0]',(nan,x));
    ceq('v[0] is v[1]-v[0]',(nan,x));
    ceq('v[0] is v[1]*v[0]',(nan,x));
    ceq('v[0] is v[1]/v[0]',(nan,x));

def rattest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  ratspectest()
  for i in xrange(repeats) :
    testops(tuple(rational(randint(*nrange),randint(*drange)) for j in xrange(3)));
  
def xtest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
  for i in xrange(repeats) :
    testops(tuple(xrational(rational(randint(*nrange),randint(*drange)),
                            rational(randint(*nrange),randint(*drange))) for j in xrange(3)));

def atest() :    # test approximate
  # verify that relative difference is within requested accuracy
  print('Approximations to e:')
  for a in range(0,257,32) :
    print('Bits of significance requested %d, actual %.2f'%(
        a, -abs(1 - e.approximate(1<<a)/e).log(2)));
  print('Approximations to pi:')
  for a in range(0,257,32) :
    print('Bits of significance requested %d, actual %.2f'%(
        a, -abs(1 - pi.approximate(1<<a)/pi).log(2)));

def sigbits(computed,actual=1) :
  if not actual :
    return 0 if computed != actual else inf;
  return -abs(1-computed/actual).log(2);

half=rational(1,2);
zero=rational(0);
one=rational(1);

def ttest() :    # test accuracy of transcendental functions
  # try values at maximum of series range:
  # exp: (imaginary arg tests sin and cos) [0,1/2]
  # ln: (v2/2,1)
  # arg (atan):  [0,v2-1]
  # sin: [-pi/27,pi/27]
  # __pow__ tests all of the above
  ceq('rational(0).exp()==1');
  ceq('rational(1).log()==0');
  ceq('rational(2).log(2)==1');
  ceq('xrational(1).arg()==0');
  ceq('xrational(0,1).arg()==hpi');
  ceq('xrational(-1,0).arg()==pi');
  ceq('xrational(1,1).arg()==qpi');
  print('(3**.5)**2 should be 3, #bits of agreement is %g'%(sigbits((3**half)**2,3)));
  print('half.exp()**2 should be e, #bits of agreement is %g'%(sigbits(half.exp()**2,e)));
  i = xrational(0,1);
  l2ri = lambda c:(-abs(c.real).log(2),-abs(c.imag).log(2));
  print('((e**(i*tau/3))**3 should be 1, #bits of agreement is %g real, %g imag'%(l2ri(1-(e**(i*tau/3))**3)));
  print('(i*tau/3).exp()**3 should be 1, #bits of agreement is %g real, %g imag'%(l2ri(1-(i*tau/3).exp()**3)));
  print('i.exp()**tau should be 1, #bits of agreement is %g real, %g imag'%(l2ri(1-i.exp()**tau)));
  print('tau.exp()**i should be 1, #bits of agreement is %g real, %g imag'%(l2ri(1-tau.exp()**i)));
  # tests of exp, ln, sin, atan ...
  # exp(ln x) = x, ln(exp(x)) = x
  # exp(ix) = cos(x) + i sin(x)
  # arg(x+iy) = atan(y/x)
  # i.e., (i*x).exp().arg() = x and abs((i*x).exp()) = 1
  bits = inf;
  for n in xrange(16) :
    x = rational(n+1,32);
    bits = min(bits,sigbits(x.exp().log(),x));
  print('min bits of agreement of ln(exp(x)) with x: %g'%(bits));
  bits = inf;
  for n in xrange(16) :
    x = (1-roothalf)*(n+1)/16;
    bits = min(bits,sigbits(x.log().exp(),x));
  print('min bits of agreement of exp(ln(x)) with x: %g'%(bits));
  bits = inf;
  for n in xrange(1,11) :
    x = rational(n,11)*hpi;
    bits = min(bits,sigbits((i*x).exp().arg(),x));
  print('min bits of agreement of arg(exp(ix)) with x: %g'%(bits));
  bits = inf;
  mbits = inf;
  for n in xrange(8) :
    x = rational(n+1,8)*froot2;
    z = ((1+i*x).arg()*i).exp();
    bits = min(bits,sigbits(z.imag/z.real,x));
    mbits = min(mbits,sigbits(z*~z,1+x*x));
  print('min bits of agreement of (i*arg(1+ix)).exp() ...');
  print('  .imag/.real with x: %g'%(bits));
  print('  .imag**2+.real**2 with 1+x**2: %g'%(bits));

def mtest(repeats=10) :    # test math functions:
# acos, acosh, asin, asinh, atan, atan2, atanh,
# ceil, copysign, cos, cosh, degrees, erf*, erfc*, exp, expm1,
# fabs*, factorial*, floor, fmod*, frexp, fsum*, gamma*, gcd+, hypot,
# isclose, isfinite*, isinf*, isnan*, ldexp*, lgamma, log, log10, log1p, log2,
# modf, pow, radians, sin, sinh, sqrt, tan, tanh, trunc*
# NOT IN math: combinations*, bernoulli*
# *: not tested below
# +: not explicitly tested, but integral to rational implementation
  rel_tol = rational(1,1<<set_significance());
  for i in xrange(repeats) :
    u = rational(random());
    x,y = floor(u),ceil(u);
    if not x <= u <= y or y-x != 1 and y != x :
      print('floor-u-ceil: %s <=? %s <=? %s'%(x.bstr(30),u.bstr(30),y.bstr(30)));
    m,p = frexp(u);
    if not (isint(p) and (not (m or p) or  .5 <= abs(m) < 1) and u == m*2**p) :
      print('frexp: %s ~ %s*2**%s'%(u.bstr(30),m.bstr(30),p.bstr(30)));
    y = ldexp(m,p);
    if u != y :
      print('ldexp(frexp(%s)) ~ %s'%(u,y));
    x = (u-half)<<8;
    f,i = modf(x);
    if i+f != x or not 0<=abs(f)<1 or copysign(1,i) != copysign(1,f) :
      print('sum(modf(%s)) ~ %s + %s'%(x.bstr(30),i.bstr(30),f.bstr(30)));
    x = (u-half)*360;
    y = degrees(radians(x));
    if x != y :
      print('degrees(radians(%s) ~ %s'%(x.btr(30),y.btr(30)));
    y = sqrt(u)**2;
    if not isclose(u,y,rel_tol=rel_tol) :
      print('sqrt(%s)**2) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = exp(log(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('exp(log(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = pow(2,log2(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('pow(2,(log2(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    y = pow(10,log10(u));
    if not isclose(u,y,rel_tol=rel_tol) :
      print('pow(10,(log10(%s)) ~ %s'%(u.bstr(30),y.bstr(30)));
    x = u/(1<<128);
    y = expm1(log1p(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('expm1(log1p(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = log1p(expm1(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('log1p(expm1(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = pi*u;
    y = acos(cos(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('acos(cos(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = pi*(u-half);
    y = asin(sin(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('asin(sin(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atan(tan(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('atan(tan(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = 128*u
    y = acosh(cosh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('acosh(cosh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = 128*(u-half);
    y = asinh(sinh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('asinh(sinh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atanh(tanh(x));
    if not isclose(x,y,rel_tol=rel_tol) :
      print('atanh(tanh(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    x = tau*(u-half);
    c = cos(x);
    s = sin(x);
    y = hypot(c,s);
    if not isclose(y,1) :
      print('hypot(cos,sin(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    y = atan2(s,c);
    if not isclose(x,y) :
      print('atan2(sin,cos(%s)) ~ %s'%(x.bstr(30),y.bstr(30)));
    
    


if __name__ == '__main__' :
  print('root test (for sha2) ...');
  roottest();
  print('rational test ...');
  rattest();
  print('xrational test ...');
  xtest();
  print('approximate test ...')
  atest();
  print('math methods test')
  mtest();
  print('transcendental function accuracy test ...')
  for significance in xrange(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE+1,gcd(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE)) :
    set_significance(significance);
    print('   significance = %d:'%(significance));
    ttest();
