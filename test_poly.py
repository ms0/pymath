from poly import *
from ffield import *
from rational import *
from random import randint, randrange, random

MINDEGREE = 1    # min degree of polynomials to be tested
MAXDEGREE = 5    # max degree of polynomials to be tested
REPEATS = 10    # number of times to repeat tests

def testf(p) :    # verify that unfactor(factor) is the identity transform
  f = p.factor();
  if p.unfactor(f) != p :
    print('%s != %s'%(p,f));
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
    print('associativity failure for %s+%s+%s'%(p,q,r));
  if (p*q)*r != p*(q*r) :
    print('associativity failure for %s+%s+%s'%(p,q,r));
  if (p+q)*r != p*r+q*r or p*(q+r) != p*q+p*r :
    print('distributivity failure for %s, %s, %s'%(p,q,r));
  if p+q != q+p :
    print('commutativity failure for %s+%s'%(p,q));
  if p*q != q*p :
    print('commutativity failure for %s*%s'%(p,q));

def testpgcd(p,q) :   # test gcd and xgcd
  g = p.gcd(q);
  h = q.gcd(p);
  if g != h :
    print('p.gcd(q) != q.gcd(p): %s, %s'%(p,q));
  if p%g or q%g :
    print('%s not a divisor of both %s and %s'%(g,p,q));
  xg = p.xgcd(q);
  xh = q.xgcd(p);
  if xg[0] != g :
    print('xgcd differs from gcd: %s != %s'%(xg[0],g));
  if g != xg[1]*p + xg[2]*q :
    print('%s != %s*%s + %s*%s'%(g,xg[1],p,xg[2],q));
  if xh[0] != g or xh[2:0:-1] != xg[1:] :
    print('p.xgcd(q) disagrees with q.gcd(p): %s, %s'(xg,xh));

def testmp() :    # test minimal polys and isirreducible
  GF243 = ffield(3,6,5);
  for k in (1,2,3,6) :
    for i in range(3**6) :
      if not polynomial(*GF243(i).minpoly(k)).isirreducible(3**k) :
        print('GF(3**6)(%d) minpoly(%d) not irreducible over GF(3**%d)?'%(i,k,k));

if __name__ == '__main__' :
  print('easy factoring test');
  GF3 = ffield(3);
  p = polynomial(1,0,2,2,0,1,1,0,2,2,0,1).mapcoeffs(GF3);
  print('unfactor test');
  f = testf(p);
  if len(f) != 3 :
    print('%s == %s, incomplete factorization'%(p,f));
  print('minpoly and isirreducible test')
  testmp();
  print('random polynomial ops test, gcd test')
  for i in range(REPEATS) :
    r = randp();
    print(map(lambda x: x.degree,r));
    testpops(*r);
    testpgcd(*r[:2])
