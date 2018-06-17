# NOTE: this tests rational.__pow__ for use in sha2.py
# NOTE: a better test of rational is part of test_matrix.py
# NOTE: a better test of rational is part of test_poly.py

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

def ceq(c,v) :
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
    ceq('not v[0] or abs(((v[0]*~v[0])-abs(v[0])**2)/(v[0]*~v[0]))<<SIGNIFICANCE < 1',v[:1])


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

def ttest() :    # test accuracy of transcendental functions
  # try values at maximum of series range:
  # exp: (imaginary arg tests sin and cos)
  # ln:
  # arg (atan):  
  # __pow__ tests all of the above
  print('(e**.5)**2/e should be 1, log2 absolute difference is %g'%(abs(1-(e**.5)**2/e).log(2)));
  print('half.exp()**2/e should be 1, log2 absolute difference is %g'%(abs(1-half.exp()**2/e).log(2)));
  i = xrational(0,1);
  l2ri = lambda c:(abs(c.real).log(2),abs(c.imag).log(2));
  print('((e**(i*tau/3))**3 should be 1, log2 absolute difference (real,imag) is %g,%g'%(l2ri(1-(e**(i*tau/3))**3)));
  print('(i*tau/3).exp()**3 should be 1, log2 absolute difference (real,imag) is %g,%g'%(l2ri(1-(i*tau/3).exp()**3)));
  print('i.exp()**tau should be 1, log2 absolute difference (real,imag) is %g,%g'%(l2ri(1-i.exp()**tau)));
  print('tau.exp()**i should be 1, log2 absolute difference (real,imag) is %g,%g'%(l2ri(1-tau.exp()**i)));

if __name__ == '__main__' :
  print('root test:   (for sha2)');
  roottest();
  print('rational test:');
  rattest();
  print('xrational test:');
  xtest();
  print('approximate test')
  atest();
  print('transcendental function accuracy test')
  ttest();
