from __future__ import print_function
from __future__ import division

import sys

if sys.version_info>(3,) :
  xrange = range;

from random import Random, randrange, sample
from itertools import chain

from timeit import timeit, default_timer

try :
  from timer import process_time
except Exception :
  process_time = default_timer;

from ffield import ffield, unpack, isprime, isirreducible, irreducibles, irreducible_count, factor, unfactor, factors, zits, gcd, lcm, gcda, lcma, phi, lam, sigma, numdivisors, divisors, getorder
from matrix import *
from poly import *

MAXCHAR = 16;    # limit on characteristics to test
LIMIT2 = 128;    # limit on ff size for full pair testing
LIMIT3 = 64;     # limit on ff size for full triple testing
LIMITM = 16;     # limit on size of vandermonde matrix
LIMITP = 32;     # limit on number of minpoly test elements
LIMITQ = 1024;   # limit on size of field for irreducibles testing

def ceq(c,*v) :
  z = v[0].__class__(0);
  o = v[0].__class__(1);
  if not eval(c) : print(c,v);

def cvs(g) :
  return ''.join(map(lambda x: zits[x],unpack(g.p,g.x)));

def dotprint(s='.') :
  sys.stdout.write(s);
  sys.stdout.flush();

def find_irr(p,n) :
  if n <= 1 : return 0;
  while True :
    x = randrange(p**n);
    tupoly = unpack(p,x);
    if isirreducible((n-len(tupoly))*(0,)+tupoly,p) : return x;

generator=None;

def randfield(p,n) :
  return ffield(p,n,find_irr(p,n));

def test(p,n) :
  global generator
  g = randfield(p,n);
  print(g);
  pn = p**n;
  if g.p != p or g.n != n or g.order != pn-1 or len(g) != pn:
    print('.p or .n or .order or len failed');
  if pn <= LIMITQ :
    ceq('v[0]==len(v[1])',irreducible_count(p,n),irreducibles(p,n));
    t=tuple(g);
    if not len(g)==len(t)==len(set(t)) :
      print('__iter__ failed');
    x = g.generator;
    ceq('v[0].generator',x);
    for y in (x,g(-1)) :
      t = tuple(g.iterpow(x));
      s = set(t);
      ceq('v[0].order==len(v[1])==len(v[2]) and v[0] in v[1] and o in v[1] and not z in v[1]',x,s,t);
  z = g(0);
  o = g(1);
  ceq('not o+-1',o);
  ceq('not -1+o',o);
  ceq('not o-1',o);
  ceq('not z-0',z);
  ceq('not 1-o',o);
  ceq('not 0-z',z);
  generator = None;
  for i in xrange(pn) :
    test1(g,i);
  if pn > LIMIT3 :
    for i in xrange(LIMIT3) :
      for j in xrange(LIMIT3) :
        for k in xrange(LIMIT3) :
          test3(g,randrange(pn),randrange(pn),randrange(pn));
  mtest(g);
  ptest(g);

def mtest(g) :    # matrix tests
  p = g.p;
  n = g.n;
  pn = p**n;
  z = g(0);
  o = g(1);
  while True :    # find an invertible matrix and verify inverse works
    M = matrix((3,3),tuple(g(randrange(pn)) for i in range(9)));
    if M.det :
      ceq('1/v[1]*v[1]==matrix.Identity(3,o)==v[1]*v[1].inverse',z,M);
      break;
  d = min(pn-1,LIMITM);    # check Vandermonde matrix determinant
  M = matrix.Identity(d,z);
  p = o;
  for i,a in enumerate(sample(xrange(1,pn),d)) :
    a = g(a);
    for j in xrange(i) :
      p *= a-M[j,1];
    for j in xrange(d) :
      M[i,j] = a**j;
  ceq('v[0]==v[1].det',p,M);

def ptest(g) :    # polynomial tests
  p = g.p;
  n = g.n;
  pn = p**n;
  for i in xrange(min(pn,LIMITP)) :
    x = g(randrange(pn));
    for m in set(chain.from_iterable((a,n//a) for a in chain((1,),factors(n)))) :
      P = polynomial(*x.minpoly(m));
      ceq('v[0].isirreducible(v[1]**v[2])',P,p,m);    # make sure irreducible
      o = p**m-1;
      ceq('v[0].degree <= v[2]//v[1]',P,m,n);    # make sure degree is not too big
      for c in P :
        ceq('not v[2] % (v[1].order or 1)',P,c,o);    # make sure coeff in GF(p**m)
      ceq('not v[0](v[1])',P,x);    # make sure element is a root

def test1(g,i) :
  global generator
  p = g.p;
  n = g.n;
  pn = p**n;
  gi = g(i);
  ceq('v[0] in v[1]',gi,g);
  if not generator and isgenerator(gi) :
    generator = gi;
    print('  generator %s'%(str(gi)));
  ceq('type(v[0])(unpack(v[0].p,v[0].x))==v[0]==type(v[0])(v[0].x)',gi);
  if p < 16 : ceq('type(v[0])(cvs(v[0]))==v[0]',gi);
  ceq('not v[0]+-v[0]',gi);
  ceq('v[0]*z==z==z*v[0]',gi);
  ceq('v[0]*0==z==0*v[0]',gi);
  ceq('v[0]*o==v[0]==o*v[0]',gi);
  ceq('v[0]*1==v[0]==1*v[0]',gi);
  ceq('v[0]-v[0]==z',gi);
  ceq('0-v[0]==-v[0]',gi);
  ceq('v[0]+1==1+v[0]',gi);
  ceq('v[0]+1-1==v[0]',gi);
  ceq('1+v[0]-1==v[0]',gi);
  ceq('1-v[0]-1==-v[0]',gi);
  if gi :
    ceq('v[0]/v[0]==o',gi);
    ceq('1/v[0]*v[0]==o',gi);
    ceq('1/v[0]==v[0]**-1',gi);
    ceq('o==v[0]**0',gi);
  if p > 2 :
    ceq('v[0]*2-v[0]==v[0]',gi);
    ceq('2*v[0]-v[0]==v[0]',gi);
    ceq('v[0]/2*2==v[0]',gi);
    if gi : ceq('2/v[0]/2==1/v[0]',gi);
  ceq('v[0]==v[0]**1',gi);
  ceq('v[0]*v[0]==v[0]**2',gi);
  for j in xrange(7) :
    for k in xrange(7) :
      ceq('v[0]**(v[1]+v[2])==v[0]**v[1]*v[0]**v[2]',gi,j,k)
      ceq('v[0]**(v[1]*v[2])==(v[0]**v[1])**v[2]',gi,j,k)
  if pn <= LIMIT2 :
    for j in xrange(pn) :
      test2(g,i,j);
      if pn <= LIMIT3 :
        for k in xrange(pn) :
          test3(g,i,j,k);
  else :
    for j in xrange(LIMIT2) :
      test2(g,i,randrange(pn));

def test2(g,i,j) :    # pair testing
  gi = g(i);
  gj = g(j);
  ceq('v[0]+v[1]==v[1]+v[0]',gi,gj);
  ceq('v[0]*v[1]==v[1]*v[0]',gi,gj);
  ceq('v[0]+v[1]-v[0]==v[1]',gi,gj);
  ceq('v[0]-v[1]+v[1]==v[0]',gi,gj);
  if gj :
    ceq('v[0]/v[1]*v[1]==v[0]',gi,gj);
    ceq('v[0]*v[1]/v[1]==v[0]',gi,gj);
  for k in xrange(7) :
    ceq('(v[0]*v[1])**v[2]==v[0]**v[2]*v[1]**v[2]',gi,gj,k);

def test3(g,i,j,k) :    # triple testing
  gi = g(i);
  gj = g(j);
  gk = g(k);
  ceq('(v[0]+v[1])+v[2]==v[0]+(v[1]+v[2])',gi,gj,gk);
  ceq('(v[0]*v[1])*v[2]==v[0]*(v[1]*v[2])',gi,gj,gk);
  ceq('v[0]*(v[1]+v[2])==v[0]*v[1]+v[0]*v[2]',gi,gj,gk);

def isgenerator(x) :
  # order of the group is p**n-1, and it's cyclic
  # if x is a generator, then x**e will be a generator for e prime to p**n-1
  # so there are phi(p**n-1) generators
  # p     n=1    n=2    n=3    n=4    n=5      table of p**n-1
  # 2      1      3      7      15     31
  #          1      2      6      8      30
  # 3      2      8      26     80    242
  #          1      4     12     32     110
  # 5      4     24     124    624   3124
  #          2      8     60    192    1400
  # 7      6     48     342   2400  16806
  #          2     16    108    640    5600
  # if x is not a generator, then for one of the prime factors qi of p**n-1,
  #   x**((p**n-1)/qi) will be 1
  if not x: return False;
  p = x.p;
  n = x.n;
  o = p**n-1;
  for q in factors(o) :
    if not x**(o//q)-1 :
      ceq('v[0].order!=v[0].__class__.order and not v[0].__class__.order%v[0].order',x);
      ceq('not v[0].generator',x);
      return False;
  ceq('v[0].order==v[0].__class__.order',x);
  ceq('v[0].generator',x);
  return True;

def ftest(*args) :
  dotprint('factor test');
  for a in args :
    try :
      for n in a : ftest1(n);
    except TypeError:
      ftest1(a);
    dotprint();
  print();

def ftest1(n) :
  f = tuple(factor(n));
  if unfactor(f) != n :
    print('unfactor(factor(%d)) failed'%(n));
  for p,k in f :
    if not isprime(p) :
      print('non primepower factor %d**%d in factor(%d)'%(p,k,n));
      break;

def gtest() :
  dotprint('gcda/lcma test');
  for i in xrange(32) :
    r = randrange(1,16);
    gtest1(tuple(randrange(1,1<<48) for _ in xrange(r)));
    dotprint();
  print();

def gtest1(a) :
  m = lcma(a);
  qs = [];
  for n in a :
    q,r = divmod(m,n);
    if r :
      print('lcm(%s) not a multiple of %d'%(args,n));
      break;
    qs.append(q);
  else :
    g = gcda(qs);
    if g > 1 :
      print('lcm(%s) too big by factor of %d'%(args,g));

def dtest() :
  dotprint('phi,lam,numdivisors,sigma,divisors,getorder test');
  for n in xrange(1,211) :
    dtest1(n);
  print();

def dtest1(n) :
  order = getorder(n);
  l = 0;     # largest order
  c = 0;     # count of elements of Zn*
  d = set(); # divisors
  for i in xrange(1,n+1) :
    o = order(i);
    if o :
      l = max(l,o);
      c += 1;
    if o < 2 and not n%i :
      d.add(i);
  if phi(n) != c :
    print('phi(%d) != %d'%(n,c));
  if numdivisors(n) != len(d) :
    print('numdivisors(%d) != %d'%(n,len(d)));
  if sigma(n) != sum(d) :
    print('sigma(%d) != %d'%(n,sum(d)));
  if lam(n) != l :
    print('lam(%d) != %d'%(n,l));
  if set(divisors(n)) != d :
    print('divisors(%d) incorrect'%(n));

R=Random();
R.seed(0);


def timing(name,G,stmt,repeats=16,nargs=1) :
  """Print time taken by stmt with nargs random args selected from G"""
  t = timeit(
    stmt=stmt if not '[i]' in stmt else
    'for i in %s(0,%d,%d):%s'%(xrange.__name__,repeats*nargs,nargs,stmt),
    setup='from ffield import ffield\nfrom test_ffield import R\nG=ffield(%d,%d)\nr=tuple(G(R.randrange(G.order+1)) for _ in %s(%d))'%(
      G.order+1,G.poly,xrange.__name__,repeats*nargs),
    timer=process_time,number=1);
  print('%s\t%s\t%f'%(G,name,t/repeats));

def timetest() :
  G = ffield(3,5);
  timing('._',G,'r[i]._n,r[i]._p,r[i]._poly,r[i]._x',1<<20);
  timing('.',G,'r[i].n,r[i].p,r[i].poly,r[i].x',1<<20);


if __name__=='__main__' :
  gtest();
  dtest();
  ftest(xrange(1,2**12+2),(2**i-1 for i in xrange(13,65)),(2**i+1 for i in xrange(13,65)));
  test(2,6);
  test(3,4);
  for p in xrange(MAXCHAR) :
    if isprime(p) :
      test(p,1);
      test(p,2);
      test(p,3);


# NOTE: we should test whether gcd is faster than exp for computing inverse
#   We did, and gcd is faster
