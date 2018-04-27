from __future__ import print_function

import sys

from poly import *
from ffield import *
from rational import *
from random import randint, randrange, random

MINDEGREE = 1    # min degree of polynomials to be tested
MAXDEGREE = 10   # max degree of polynomials to be tested
OPREPEATS = 10   # number of times to repeat operation tests
FREPEATS = 100   # number of times to repeat factoring tests

def error(*args,**kwargs) :
  print(file=sys.stderr);
  print(*args,file=sys.stderr,**kwargs);

def dotprint(s='.') :
  sys.stdout.write(s);
  sys.stdout.flush();

def testf(p) :    # verify that unfactor(factor) is the identity transform
  dotprint('%x'%(p.degree));
  f = p.factor();
  if p.unfactor(f) != p :
    error('%s != %s'%(p,f));
  for q in f :
    if not q.isirreducible() :
      error('factor %s is not irreducible over %s'%(q,q[0].__class__));
  return f;

def randp() :
  p = [];
  for i in range(3) :    # make 3 random polynomials
    degree = randint(MINDEGREE,MAXDEGREE);
    p.append(polynomial(*tuple(random() for j in range(degree+1))));
    p[-1] = p[-1].mapcoeffs(rational);
  return p;

def testpops(p,q,r) :    # test polynomial operations
  # test associativity, distributivity, commutativity
  if (p+q)+r != p+(q+r) :
    error('associativity failure for %s+%s+%s'%(p,q,r));
  if (p*q)*r != p*(q*r) :
    error('associativity failure for %s+%s+%s'%(p,q,r));
  if (p+q)*r != p*r+q*r or p*(q+r) != p*q+p*r :
    error('distributivity failure for %s, %s, %s'%(p,q,r));
  if p+q != q+p :
    error('commutativity failure for %s+%s'%(p,q));
  if p*q != q*p :
    error('commutativity failure for %s*%s'%(p,q));

def testpgcd(p,q) :   # test gcd and xgcd
  g = p.gcd(q);
  h = q.gcd(p);
  if g != h :
    error('p.gcd(q) != q.gcd(p): %s, %s'%(p,q));
  if p%g or q%g :
    error('%s not a divisor of both %s and %s'%(g,p,q));
  xg = p.xgcd(q);
  xh = q.xgcd(p);
  if xg[0] != g :
    error('xgcd differs from gcd: %s != %s'%(xg[0],g));
  if g != xg[1]*p + xg[2]*q :
    error('%s != %s*%s + %s*%s'%(g,xg[1],p,xg[2],q));
  if xh[0] != g or xh[2:0:-1] != xg[1:] :
    error('p.xgcd(q) disagrees with q.gcd(p): %s, %s'(xg,xh));

def testmp(F) :    # test minimal polys and isirreducible in ffield F
  print('%s'%(F));
  p = F.p;
  n = F.n;
  for k in range(1,n) :
    if n%k : continue;
    for i in range(p**n) :
      dotprint();
      if not polynomial(*F(i).minpoly(k)).isirreducible(p**k) :
        error('GF(%d**%d)(%d) minpoly(%d) not irreducible over GF(%d**%d)?'
              %(p,n,i,k,p,k));

if __name__ == '__main__' :
  GF3 = ffield(3);
  p = polynomial(1,0,2,2,0,1,1,0,2,2,0,1).mapcoeffs(GF3);
  print('factor test');
  f = testf(p);
  GF243 = ffield(3,6,5);
  GF64 = ffield(2,6,3);
  GF32 = ffield(2,5,5);
  for F in (GF243,GF64,GF32) :
    print('\n%s'%(F));
    for i in range(FREPEATS) :
      testf(polynomial(F(1),*(F(randrange(F.order+1))
                              for j in range(randint(MINDEGREE,MAXDEGREE)))));
  print('\nminpoly and isirreducible test')
  testmp(GF243);
  print('\nrandom polynomial ops test, gcd test')
  for i in range(OPREPEATS) :
    r = randp();
    print(map(lambda x: x.degree,r));
    testpops(*r);
    testpgcd(*r[:2]);
  print('\nCompleted');
