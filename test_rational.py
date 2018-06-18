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


def rattest(repeats=1000,nrange=(-100,100),drange=(1,100)) :
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

def ttest() :    # test accuracy of transcendental functions
  # try values at maximum of series range:
  # exp: (imaginary arg tests sin and cos) [0,1/2]
  # ln: (v2/2,1)
  # arg (atan):  [0,v2-1]
  # sin: [-pi/27
  # __pow__ tests all of the above
  ceq('rational(0).exp()==1');
  ceq('rational(1).log()==0');
  ceq('rational(2).log(2)==1');
  ceq('xrational(1).arg()==0');
  ceq('xrational(0,1).arg()==hpi');
  ceq('xrational(-1,0).arg()==pi');
  ceq('xrational(1,1).arg()==qpi');
  print('(e**.5)**2 should be e, #bits of agreement is %g'%(sigbits((e**.5)**2,e)));
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
  for n in xrange(8) :
    x = rational(n+1,16);
    bits = min(bits,sigbits(x.exp().log(),x));
  print('min bits of agreement of ln(exp(x)) with x: %g'%(bits));
  bits = inf;
  for n in xrange(8) :
    x = (1-roothalf)*(n+1)/8;
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
  print('  .imag**2+.real**2) with 1+x**2: %g'%(bits));


if __name__ == '__main__' :
  print('root test (for sha2) ...');
  roottest();
  print('rational test ...');
  rattest();
  print('xrational test ...');
  xtest();
  print('approximate test ...')
  atest();
  print('transcendental function accuracy test ...')
  for significance in xrange(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE+1,gcd(MIN_SIGNIFICANCE,MAX_SIGNIFICANCE)) :
    set_significance(significance);
    print('   significance = %d:'%(significance));
    ttest();
