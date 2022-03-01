from __future__ import print_function
from __future__ import division

import sys

from random import Random
from rational import rational
from numbers import primepower,divisors,isirreducible,irreducible_count,zits
from poly import polynomial,rationalfunction
from ffield import ffield
from ffpoly import irreducibles

R=Random();
randint=R.randint;
randrange=R.randrange;
random=R.random;
R.seed(0);    # for reproducibility of tests

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
  dotprint(zits[p.degree] if p else '-');
  f = p.factor();
  if p.unfactor(f) != p :
    error('%s != %s'%(p,f));
  for q in f :
    if q.degree > 1 and not q.isirreducible() :
      error('factor %s is not irreducible over %s'%(q,type(q[0])));
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
  if q and r and (p*r)/(q*r) != p/q :
    error('division failure for %s, %s, %s'%(p,q,r));
  if q and (p*q)/q != p :
    error('division failure for %s, %s'%(p,q));
  if p+q != q+p :
    error('commutativity failure for %s+%s'%(p,q));
  if p*q != q*p :
    error('commutativity failure for %s*%s'%(p,q));
  if p**5*p != p**6 :
    error('failure for %s**6'%(p));
  if pow(q,5,r) != pow(q,5)%r :
    error('failure for pow(%s,5,%s)'%(q,r));
  if p<<3 != p>>-3 or p<<-3 != p>>3 :
    error('failure of %s<<3 or <<-3 or >>3 or >>-3'%(p));
  if ((p<<3)>>3) != p :
    error('failure for (%s<<3)>>3'%(p));
  if ((p>>3)<<3) != p :
    error('failure for (%s>>3)<<3'%(p));

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
    error('p.xgcd(q) disagrees with q.gcd(p): %s, %s'%(xg,xh));

def testmp(F) :    # test minimal polys and isirreducible in ffield F
  print('%s'%(F.__name__));
  p = F.p;
  n = F.n;
  for k in divisors(n) :
    for g in F :
      dotprint();
      f = g.minpolynomial(k);
      if not f :
        error('%r.minpoly(%d) is 0?'%(g,k));
      o = p**k-1;
      for c in f :
        if o%(c.order or 1) :
          error('coeff %r of %r.minpoly(%d) not in GF(%d**%d)'%(c,g,k,p,k));
      if f(g) :
        error('%r not a root of its minpoly(%d)?'%(g,k));
      if not f.isirreducible(p**k) :
        error('%r.minpoly(%d) not irreducible over GF%d_%d?'%(g,k,p,k));
      if (g.order==p**(k*f.degree)-1) != f.isprimitive(p**k) :
        error('isprimitive failed for %r.minpoly(%d)'%(g,k));

def testir(F) :    # test irreducibles
  dotprint('\n%s '%(F.__name__) );
  for i in range(2,10) :
    if F.q**i > 1000 : break;
    dotprint(zits[i]);
    if len(irreducibles(F,i)) != irreducible_count(F.q,i) :
      error('len(irreducibles(%d,%d)) incorrect'%(F.q,i));

def factest(F) :
  dotprint('\n%s '%(F.__name__));
  for i in range(FREPEATS) :
    testf(polynomial(*(F(randrange(F.order+1))
                       for j in range(randint(1+MINDEGREE,1+MAXDEGREE)))));

def factests() :
  GF2 = ffield(2);
  GF3 = ffield(3);
  p = polynomial(1,0,2,2,0,1,1,0,2,2,0,1).mapcoeffs(GF3);
  dotprint('%s '%(GF3.__name__));
  testf(p);
  p = polynomial(GF2(1));  # try product of all irreducible polys mod 2 thru degree 4
  for d in range(1,5) :
    for i in range(2**d) :
      t = tuple(map(int,format(i,'0%db'%(d))));
      if isirreducible(t,2) : p *= polynomial(*(1,)+t).mapcoeffs(GF2);
  dotprint('  %s '%(GF2.__name__));
  testf(p);
  GF729 = ffield(729);
  GF64 = ffield(64);
  GF32 = ffield(32);
  for F in (GF729,GF64,GF32) :
    factest(F);

def optests() :
  for i in range(OPREPEATS) :
    r = randp();
    print(tuple(map(lambda x: x.degree,r)));
    testpops(*r);
    testpgcd(*r[:2]);

def testattr() :
  x = polynomial(1,0);
  o = polynomial(1);
  z = polynomial();
  ox= rationalfunction(o,x);
  if not x == x.a == x.numerator :
    print('x.a or x.numerator failed');
  if not o == x.b == x.denominator :
    print('x.b or x.denominator failed');
  if x.degree != 1 :
    print('x.degree failed');
  if not o == ox.a == ox.numerator or not x == ox.b == ox.denominator :
    print('ox.a or ox.b or ox.numerator or ox.denominator failed');
  if ox.degree != -1 :
    print('ox.degree failed');

if __name__ == '__main__' :
  print('attribute test');
  testattr();
  print('factor test');
  factests();
  GF729 = ffield(3,6);
  print('\nminpoly, isirreducible, isprimitive test')
  for q in (2,3,5,7,11,2**6,5**4,3**6) :
    testmp(ffield(q));
  dotprint('\nirreducibles test')
  for q in range(32) :
    if primepower(q) : testir(ffield(q));
  print('\nrandom polynomial ops test, gcd test')
  optests();
  print('\nCompleted');
