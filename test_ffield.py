from __future__ import print_function
from __future__ import division

import sys

if sys.version_info>(3,) :
  xrange = range;

from random import Random, randrange, sample
from itertools import chain, count

from timeit import timeit, default_timer

try :
  from timer import process_time
except Exception :
  process_time = default_timer;

from ffield import *
from numbers import unpack, isprime, isirreducible, irreducibles, irreducible_count, isprimitive, factor, unfactor, factors, zits, gcd, lcm, gcda, lcma, phi, lam, sigma, numdivisors, divisors, getorder, primes
from matrix import *
from poly import *

MAXCHAR = 10;    # limit on characteristics to test
LIMIT2 = 64;     # limit on ff size for full pair testing
LIMIT3 = 16;     # limit on ff size for full triple testing
LIMITM = 16;     # limit on size of vandermonde matrix
LIMITP = 32;     # limit on number of minpoly test elements
LIMITQ = 1024;   # limit on size of field for irreducibles testing
LIMITL = 256;    # limit on number of log tests (and size of field to be tested)

z,o = 0,1;    # replaced by field elements

def ceq(c,*v) :
  try :
    if not eval(c) : print(c,v);
  except Exception:
    print(c,v);
    raise;

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

def randfield(p,n) :
  return ffield(p,n,find_irr(p,n));

def test(p,n) :
  global z,o
  g = randfield(p,n);
  q = g.q;
  if g.p != p or g.n != n or g.order != q-1 or len(g) != q:
    print('.p or .n or .q or .order or len failed');
  atest(g);

def atest(g) :
  print('%s  generator %s'%(g.__name__,g.generator));
  ctest(g);
  otest(g);
  rtest(g);
  mtest(g);
  ptest(g);
  ltest(g);  

def otest(g) :
  global z,o
  z,o = g[:2];
  p = g.p;
  n = g.n;
  q = g.q;
  if q <= LIMIT2 :
    if tuple(g) != g[:] :
      print('__iter__ or slice indexing failed');
    for i in xrange(q) :
      if not g[i] == g[i-q] == g(i) :
        print('indexing failed');
  x = g.generator;
  ceq('isgenerator(v[0])',x);
  if q <= LIMITQ :
    if irreducible_count(p,n) != len(irreducibles(p,n)) :
      print('GF(%d**%d) irreducible_count != len(irreducibles)'%(p,n));
    t=tuple(g);
    if not len(g)==len(t)==len(set(t)) :
      print('__iter__ failed');
    for y in (x,-o,g[-1]) :
      t = tuple(g.iterpow(y));
      s = set(t);
      ceq('v[0].order==len(v[1])==len(v[2]) and v[0] in v[1] and o in v[1] and not z in v[1]',y,s,t);
      t = tuple(g.iterpow(y,alt=1));
      s = set(t);
      ceq('v[0].order==len(v[1])==len(v[2]) and v[0] in v[1] and o in v[1] and not z in v[1]',y,s,t);
  ceq('not o+-1');
  ceq('not -1+o');
  ceq('not o-1');
  ceq('not z-0');
  ceq('not 1-o');
  ceq('not 0-z');
  dotprint('  op tests');
  for i in xrange(q) :
    test1(g,i);
    if not i%(q//32 or 1) : dotprint();
  print();
  if q > LIMIT3 :
    dotprint('  random triples test');
    for i in xrange(LIMIT3) :
      for j in xrange(LIMIT3) :
        for k in xrange(LIMIT3) :
          test3(g(randrange(q)),g(randrange(q)),g(randrange(q)));
      if not i%(LIMIT3//32 or 1) : dotprint();
    print();

def ltest(g) :    # log test
  print('  log tests');
  p = g.p;
  n = g.n;
  q = g.q;
  o = q-1;
  g1 = g.generator;
  g2 = 1/g1;
  for e in xrange(min(o,17)) :
    ceq('v[0]==v[1]**v[0].log(v[1])',g1**e,g2);
    ceq('v[0]==v[1]**v[0].log(v[1],True)',g1**e,g2);
    ceq('v[0]==v[1]**v[0].log(v[1])',g2**e,g1);
    ceq('v[0]==v[1]**v[0].log(v[1],True)',g2**e,g1);
  if o <= LIMITL :
    for i in xrange(LIMITL) :
      v = list(g(randrange(1,q)) for j in xrange(2));
      vo = list(map(lambda x:x.order,v));
      for k in xrange(2) :
        if vo[1]%vo[0] :
          try :
            v[0].log(v[1]);
            print('%s.log(%s) should fail'%(v[0],v[1]));
          except ValueError :
            pass;
        else :
          ceq('v[0]==v[1]**v[0].log(v[1])',*v);
        v = v[-1::-1];
        vo = vo[-1::-1];

def ctest(g) :    # comparison and contains tests
  print('  field comparison and contains tests')
  ceq('v[0].basefield<=v[0]',g);
  ceq('v[0]>=v[0].basefield',g);
  ceq('not v[0].basefield>v[0]',g);
  ceq('not v[0]<v[0].basefield',g);
  for i in xrange(g.basefield.q) :
    gi = g(i);
    bi = g.basefield(i);
    ceq('v[0] in type(v[1])',bi,gi);
    ceq('v[1] in type(v[0])',bi,gi);
    ceq('type(v[0])(v[1])==type(v[1])(v[0])',bi,gi);
  if g.q > g.basefield.q :
    ceq('not v[0](v[0].basefield.q) in v[0].basefield',g);

def mtest(g) :    # matrix tests
  global z,o
  z,o = g[:2];
  print('  matrix tests');
  p = g.p;
  n = g.n;
  q = g.q;
  while True :    # find an invertible matrix and verify inverse works
    M = matrix((3,3),tuple(g(randrange(q)) for i in xrange(9)));
    if M.det :
      ceq('1/v[0]*v[0]==matrix.Identity(3,o)==v[0]*v[0].inverse',M);
      break;
  d = min(q-1,LIMITM);    # check Vandermonde matrix determinant
  M = matrix.Identity(d,z);
  x = o;
  for i,a in enumerate(sample(xrange(1,q),d)) :
    a = g(a);
    for j in xrange(i) :
      x *= a-M[j,1];
    for j in xrange(d) :
      M[i,j] = a**j;
  ceq('v[0]==v[1].det',x,M);

def ptest(g) :    # polynomial tests
  print('  polynomial tests')
  p = g.p;
  n = g.n;
  q = g.q;
  for i in xrange(min(q,LIMITP)) :
    x = g(randrange(q));
    for m in set(chain.from_iterable((a,n//a) for a in chain((1,),factors(n)))) :
      P = x.minpolynomial(m);
      if not P.isirreducible(p**m) :
        print('%r.minpoly(%d) not irreducible'%(x,m));
      d = P.degree;
      if (x.order==(p**d-1))!=isprimitive(P.mapcoeffs(int)[-2::-1],p) if m==1 else \
         (x.order==p**(m*d)-1) != P.isprimitive(p**m) :
        print('isprimitive(%r.minpoly(%d)) failed'%(x,m));
      o = p**m-1;
      if d > n//m :
        print('%r.minpoly(%d) degree > %d/%d'%(x,m,n,m));
      for c in P :
        if o%(c.order or 1) :
          print('coeff %r of %r.minpoly(%d) not in GF(%d**%d)'%(c,x,m,p,m));
      if P(x) :
        print('%r not a root of its minpoly(%d)'%(x,m));

def rtest(g) :    # mixed ffields test
  f = g.basefield;
  e = f.basefield;
  if f != g :
    dotprint('  mixed fields test');
    if g.q <= LIMIT2 :
      for i in g :
        for j in f :
          test2(i,j);
        dotprint();
    else :
      for n in xrange(LIMIT2) :
        i = g(randrange(g.q));
        if f.q <= LIMIT2 :
          for j in f :
            test2(i,j);
        else :
          for m in xrange(LIMIT2) :
            j = f(randrange(f.q));
            test2(i,j);
        if e != f :
          if e.q <= LIMIT2 :
            for j in e :
              test2(i,j);
          else :
            for m in xrange(LIMIT2) :
              j = e(randrange(e.q));
              test2(i,j);
        dotprint();
    print();

def test1(g,i) :
  global z,o
  z,o = g[:2];
  p = g.p;
  n = g.n;
  q = g.q;
  gi = g(i);
  isgenerator(gi);
  ceq('v[0] in v[1]',gi,g);
  if not ((i in g) == (-i in g) == (abs(i) < p)) :
    print('+-%d in g failed'%(i));
  ceq('type(v[0])(v[0])==v[0]',gi);
  ceq('type(v[0])(-v[0].x)==-v[0]',gi);
  try :
    f = g.basefield;
    ceq('type(v[0])(unpack(type(v[0]).basefield.q,v[0].x))==v[0]==type(v[0])(v[0].x)',gi);
    ceq('type(v[0])(map(lambda x:-x,unpack(type(v[0]).basefield.q,v[0].x)))==-v[0]',gi);
    ceq('type(v[0])(polynomial(*(unpack(type(v[0]).basefield.q,v[0].x))))==v[0]',gi);
  except Exception :
    ceq('type(v[0])(unpack(v[0].p,v[0].x))==v[0]==type(v[0])(v[0].x)',gi);
    ceq('type(v[0])(map(lambda x:-x,unpack(v[0].p,v[0].x)))==-v[0]',gi);
    ceq('type(v[0])(polynomial(*(unpack(v[0].p,v[0].x))))==v[0]',gi);
  if p < 36 : ceq('type(v[0])(cvs(v[0]))==v[0]',gi);
  ceq('not v[0]+-v[0]',gi);
  ceq('v[0]*z==z==z*v[0]',gi);
  ceq('v[0]*0==z==0*v[0]',gi);
  ceq('v[0]*o==v[0]==o*v[0]',gi);
  ceq('v[0]*1==v[0]==1*v[0]',gi);
  ceq('v[0]*-1==-v[0]==-1*v[0]',gi);
  ceq('v[0]-v[0]==z',gi);
  ceq('0-v[0]==-v[0]',gi);
  ceq('v[0]+1==1+v[0]',gi);
  ceq('v[0]+1-1==v[0]',gi);
  ceq('1+v[0]-1==v[0]',gi);
  ceq('1-v[0]-1==-v[0]',gi);
  ceq('-1-v[0]+1==-v[0]',gi);
  ceq('-1+v[0]+1==v[0]',gi);
  if gi :
    ceq('v[0]/v[0]==o',gi);
    ceq('1/v[0]*v[0]==o',gi);
    ceq('-1/v[0]*v[0]==-o',gi);
    ceq('1/v[0]==v[0]**-1',gi);
    ceq('o==v[0]**0',gi);
  if p > 2 :
    ceq('v[0]*2-v[0]==v[0]',gi);
    ceq('2*v[0]-v[0]==v[0]',gi);
    ceq('v[0]/2*2==v[0]',gi);
    if gi : ceq('2/v[0]/2==1/v[0]',gi);
  else :
    ceq('v[0]*2==z==2*v[0]',gi);
    if gi : ceq('2/v[0]==z',gi);
  ceq('v[0]==v[0]**1',gi);
  ceq('v[0]*v[0]==v[0]**2',gi);
  for j in xrange(7) :
    for k in xrange(7) :
      ceq('v[0]**(v[1]+v[2])==v[0]**v[1]*v[0]**v[2]',gi,j,k)
      ceq('v[0]**(v[1]*v[2])==(v[0]**v[1])**v[2]',gi,j,k)
  if q <= LIMIT2 :
    for j in xrange(q) :
      test2(g(i),g(j));
      if q <= LIMIT3 :
        for k in xrange(q) :
          test3(g(i),g(j),g(k));
  else :
    for j in xrange(LIMIT2) :
      test2(g(i),g(randrange(q)));

def test2(i,j) :    # pair testing
  ceq('v[0]+v[1]==v[1]+v[0]',i,j);
  ceq('v[0]-v[1]==-(v[1]-v[0])',i,j);
  ceq('v[0]*v[1]==v[1]*v[0]',i,j);
  if i and j :
    ceq('v[0]/v[1]==1/(v[1]/v[0])',i,j);
  for k in xrange(7) :
    ceq('(v[0]*v[1])**v[2]==v[1]**v[2]*v[0]**v[2]',i,j,k);

def test3(i,j,k) :    # triple testing
  ceq('(v[0]+v[1])+v[2]==v[0]+(v[1]+v[2])',i,j,k);
  ceq('(v[0]*v[1])*v[2]==v[0]*(v[1]*v[2])',i,j,k);
  ceq('v[0]*(v[1]+v[2])==v[0]*v[1]+v[0]*v[2]',i,j,k);

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
      ceq('v[0].order!=type(v[0]).order and not type(v[0]).order%v[0].order',x);
      ceq('not v[0].generator',x);
      return False;
  ceq('v[0].order==type(v[0]).order',x);
  ceq('v[0].generator',x);
  return True;

def ftest(*args) :
  dotprint('(integer) factor/unfactor/isprime test');
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
  dotprint('phi/lam/numdivisors/sigma/divisors/getorder test');
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
    setup='from ffield import _ffield\nfrom test_ffield import R\nG=_ffield[%s]\nr=tuple(G(R.randrange(G.q)) for _ in %s(%d))'%(
      G.id,xrange.__name__,repeats*nargs),
    timer=process_time,number=1);
  print('%s\t%s\t%.6f'%(G.__name__,name,t/repeats));

def timetest(g) :
  timing('-x',g,'-r[i]',1<<10);
  timing('1/x',g,'1/(r[i] or r[i]+1)',1<<10);
  timing('x**-1',g,'(r[i] or r[i]+1)**-1',1<<10);
  timing('x+y',g,'r[i]+r[i+1]',1<<10,2);
  timing('x*y',g,'r[i]*r[i+1]',1<<10,2);
  timing('x/y',g,'r[i]/(r[i+1] or r[i+1]+1)',1<<10,2);
  timing('x**y',g,'r[i]**r[i+1].x',1<<10,2);
  timing('minpoly',g,'r[i].minpoly()',1<<7);
  if g.q <= 1<<10 :
    timing('log',g,'(r[i] or r[i]+1).log()',1<<7);
    timing('logalt',g,'(r[i] or r[i]+1).log(alt=1)',1<<7);

if __name__=='__main__' :

  def usage() :
    print("""
Usage: python test_ffield.py [options]
   Options:  -h        print this message
             -x        exclude integer tests
             -z q      max field size to test [default 81 (i.e., 3**4)]
             -r        test ffieldx
             -c q      print Conway polys up to max field size q with p^4 <= q
             -t        print timing info""");

  import sys,getopt
  opts,args = getopt.gnu_getopt(sys.argv[1:],"hxrtz:c:");
  optdict = {};
  for pair in opts : optdict[pair[0][1:]]=pair[1];
  if 'h' in optdict :
    usage();
    sys.exit();
  if not 'x' in optdict :
    gtest();
    dtest();
    ftest(xrange(1,2**12+2),(2**i-1 for i in xrange(13,65)),(2**i+1 for i in xrange(13,65)));
  q = int(optdict.get('z',3**4));
  for p in xrange(MAXCHAR) :
    if isprime(p) :
      for i in range(1,7) :
        if p**i <= q : test(p,i);
  if 'r' in optdict :
    F4 = ffield(4);
    F9 = ffield(9);
    F16 = ffieldx(polynomial(1,F4(2),1));
    F81 = ffieldx(polynomial(1,F9(4),1));
    F256 = ffieldx(polynomial(1,F16(4),1));
    for g in (F81,F256) : atest(g);
  if 'c' in optdict :
    print('Conway polynomials')
    q = int(optdict['c']);
    for p in primes() :
      if p**4 >= q : break;
      for i in count(1) :
        if p**i > q : break;
        print(p,i,unpack(p,conwaypoly(p**i)));
  if 't' in optdict :
    for g in (ffield(2,8),ffield(3,5),    # pairs with similar sizes
              ffield(2,9),ffield(23,2),
              ffield(2,17),ffield(19,4),
              ffield(2**2**4+1),
              ffield(2**61-1),
              ffield(2**61)) :
      timetest(g);
    if 'r' in optdict :
      for g in (F81,F256) : timetest(g);

# NOTE: we should test whether gcd is faster than exp for computing inverse
#   We did, and gcd is faster
