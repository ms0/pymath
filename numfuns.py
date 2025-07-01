from __future__ import division

import random
random.seed();

from itertools import chain, count
from matrix import matrix, product
from conversions import isint, gcd, gcda, lcm, lcma, xrange, bit_length, bit_count, pack
from rational import root, rint, xgcd

def modpow(b,x,p) :    # b**x mod p
  """Compute b**x%p"""
  if not x : return 1;
  n = (1 << (bit_length(x)-1)) >> 1;
  e = b%p;
  while n :
    e *= e;
    e %= p;
    if x&n :
      e *= b;
      e %= p;
    n >>= 1;
  return e;

primalitytestlimit = 1<<24;    # limit for looking for (odd) divisor
# beyond this limit, use Miller-Rabin or Lucas-Lehmer

pr210 = (2,3,5,7,11,13);    # primes < sqrt(2*3*5*7)
isp210 = tuple(    # primality of integers in range(2*3*5*7)
  i in pr210 or i > pr210[-1] and all(i%p for p in pr210) for i in xrange(210));
op210 = pr210[1:] + tuple(    # odd primes < 2*3*5*7
  i for i in xrange(pr210[-1]+1,210) if isp210[i]);
isZ210 = tuple(gcd(i,210)==1 for i in xrange(210));    # relative primality mod 2*3*5*7
Z210 = tuple(i for i in xrange(210) if isZ210[i]);    # relative primes mod 2*3*5*7

def oplist(m) :    # odd primes < 2*3*5*7 then larger ints relatively prime to 2*3*5*7
  for i in op210 : yield i;
  for i in xrange(210,m,210) if m else count(210,210):    # give up after m
    for p in Z210 : yield i+p;

def oplist11(m) : # oplist, but starting at 11
  for i in op210[3:] : yield i;
  for i in xrange(210,m,210) if m else count(210,210):    # give up after m
    for d in Z210 : yield i+d;

def nextprime(x) :
  """Return smallest prime > x"""
  for p in primes(int(x)+1) :
    return p;

def primes(start=2,stop=None) :
  """Generator for primes"""
  if stop is None :
    if start <= 2 :
      yield 2;
      for p in op210: yield p;
      for i in count(210,210) :
        for d in Z210 :
          p = i+d;
          if isprime(p) : yield p;
    else :
      z = start-start%210;
      if z :
        for d in Z210 :
          p = z+d;
          if start <= p and isprime(p) : yield p;
      else :
        for p in op210:
          if start <= p : yield p;
      for i in count(z+210,210) :
        for d in Z210 :
          p = i+d;
          if isprime(p) : yield p;
  elif start < stop :
    if start <= 2 < stop :
      yield 2;
    z = start-start%210;    # initial tranche
    t = stop-stop%210;      # final tranche
    if not z :    # start in [0,210)
      if t :
        for p in op210 :
          if start <= p : yield p;
      else :    # start and end in [0,210)
        for p in op210 :
          if p >= stop : return;
          if start <= p : yield p;
        return;
    else :    # start from 210 or greater
      if z < t :
        for d in Z210 :
          p = z+d;
          if start <= p and isprime(p) : yield p;
      else :    # start and end in same tranche
        for d in Z210 :
          p = z+d;
          if p >= stop : return;
          if start <= p and isprime(p) : yield p;
        return;
    for i in xrange(z+210,t,210) :    # full tranches
      for d in Z210 :
        p = i+d;
        if isprime(p) : yield p;
    for d in Z210 :    # final tranche
      p = t+d;
      if p >= stop : return;
      if isprime(p) : yield p;
  
def isprime(n) :
  """Test if n is prime, if no "small" factors,
use probabilistic Miller-Rabin test or Lucas-Lehmer test when applicable"""
  n = rint(n);
  if n < 210 : return isp210[n];
  if not isZ210[n%210] : return False;
  if n&(n+1) :    # not Mersenne number
    if (n-1)&(n-2):    # not Fermat number
      d = oplist11(primalitytestlimit);    # general primality test
    else :
      e = bit_length(n)-1;    # n = 2**e+1 [Fermat?]
      if e&(e-1) : return False;    # e not power of 2
      return pow(3,n>>1,n)==n-1;    # Pepin's test
    for p in d :
      q,r = divmod(n,p);
      if not r : return False;
      if q <= p : return True;
    # Miller Rabin test :
    c = n-1;
    b = bit_length(c&-c)-1;
    c >>= b;    # n-1 = 2**b * c
    for i in xrange(100) :
      a = random.randrange(2,n-1);
      e = pow(a,c,n);
      if e == 1 : continue;
      for i in xrange(b) :
        if e == n-1 : break;
        e = pow(e,2,n);
        if e == 1 : return False;
      else :
        return False;    # didn't get to -1
    return True;
  e = bit_length(n);    # n = 2**e-1 [Mersenne?]
  if not isprime(e) : return False;    # e not prime
  for i in xrange(2*e+1,primalitytestlimit,2*e) :
    # prime factors must be 2ke+1 and +-1 mod 8
    if (i+1)&7 > 2 or not isZ210[i%210]: continue;
    q,r = divmod(n,i);
    if not r: return False;
    if q <= i : return True;
  # Lucas-Lehmer test :
  c = 4;
  for i in xrange(e-2) :
    c = (c*c-2)%n;
  return not c;

bigp = 53;    # "big" prime
lps = set(primes(2,bigp));    # "little" primes
plps = product(lps);   # product of "little" primes

def primepower(q) :
  """Return (p,n) if q == p**n, else None"""
  g = gcd(plps,q);
  if g != 1 :
    if not g in lps : return None;
    if g == 2 :
      c = bit_length(q&-q)-1;
      q >>= c;
      return (2,c) if q==1 else None;
    for c in count(1) :
      q,r = divmod(q,g);
      if r : return None;
      if q == 1 : return (g,c);
  x = 1;
  for p in primes() :
    while True :
      if bigp**p > q : return (q,x) if isprime(q) else None;
      r = root(q,p);
      if r**p != q : break;
      x *= p;
      q = r;

# test for irreducibility [Rabin]
# let p be our prime, and n our exponent
# let q1, q2,..., qk be all the distinct prime divisors of n, in ascending order
# let f be a monic polynomial in Fp[x] of degree n
# for j = 1 thru k
#   nj = n/qj
# for i = 1 thru k
#   h = x**p**ni - x mod f
#   g = gcd(f,h)
#   if g != 1, f is reducible
# g = x**p**n - x mod f
# if g != 0 f is reducible
# else f is irreducible

x = (1,0);
one = (1,);

def isirreducible(poly,q) :  # missing leading coefficient assumed to be 1
  """Run the deterministic Rabin test to see if poly is irreducible over GF(q);
q must be a positive power of a prime p; poly is represented as a tuple of
integer coefficients interpreted mod p, ending with the constant term, but
without the leading coefficient, which is taken to be 1"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p,k = p;
  n = len(poly);
  if n <= 1 : return n==1;
  if not poly[-1] : return False;
  f = one+poly;
  if p == 2 : return isirreducible2(pack(2,f),k);
  for r in factors(n) :
    if len(mpgcd(p,f,mpsub(p,mppow(p,x,q**(n//r),f),x))) != 1 : return False;
  return not mpsub(p,mppow(p,x,q**n,f),x);

# An irreducible polynomial f(x) of degree m over GF(p), where p is prime,
# is a primitive polynomial iff the smallest positive integer n such that
# f(x) | x^n - 1 is n = p^m - 1.

def isprimitive(g,p) :
  """Return True iff monic irreducible g is a primitive polynomial over GF(p);
  g is represented as a tuple or list of integers mod p without the leading 1"""
  n = len(g);
  if p == 2 : return isprimitive2((1<<n)|pack(2,g));
  q = primepower(p);
  if not q : raise ValueError('p must be a prime');    # but allow prime power
  if q[1] != 1 or not g[-1] : return False;
  if n == 1 and g[0] == p-1 : return False;    # x-1
  o = p**n-1;
  og = one+g;
  for f in ffactors(o) :
    if mppow(p,x,o//f,og) == one : return False;
  return True;

def ffactors(n) :
  """Memoized and return the prime factors of n in increasing order as a generator"""
  for p in ffactor(n) : yield p[0];

def factors(n,maxfactor=None) :
  """Return the prime factors of n in increasing order as a generator; but
     the final factor may not be prime if > maxfactor"""
  for p in factor(n,maxfactor) : yield p[0];

def leastfactor(n,maxfactor=None) :
  """Return the smallest prime factor of n, or 1 if no prime factor; but
     the factor returned max not be prime if > maxfactor"""
  for p in factors(n,maxfactor) :
    return p;
  return 1;

_ffactorization = dict();    # full factorizations

def ffactor(n) :
  """Memoize and return the factorization of n as a tuple of (prime,exponent) pairs"""
  try :
    return _ffactorization[n];
  except KeyError :
    _ffactorization[n] = f = tuple(factor(n));
    return f;    

def factor(n,maxfactor=None) :
  """Return prime factorization of n as generator of (prime,exponent) pairs; but
     if the final factor has exponent 1, it may not be a prime if > maxfactor"""
  n = abs(n);
  if n <= 1 :
    return;
  try :
    for px in _ffactorization[n] :
      yield px;
    return;
  except KeyError :
    pass;
  if not n & 1:
    c = bit_length(n&-n)-1;
    n >>= c;
    yield (2,c);
  if n > primalitytestlimit and isprime(n) :
    yield (n,1);
    return;
  d = oplist(maxfactor);
  if not n&(n+1) :
    if n == 1 : return;
    e = bit_length(n);    # 2**e-1
    if isprime(e) :
      d = xrange(2*e+1,maxfactor,2*e) if maxfactor else count(2*e+1,2*e);
    else :
      f = tuple(factor(e));
      g = [];
      for q,k in f :
        if len(f) == 1 : k-=1;
        x = (1<<(q**k))-1;
        g.append(x);
        n //= x;
      g.append(n);
      for p in fmerge(*map(factor,g)) : yield p;
      return;
  elif not (n-1)&(n-2) :
    e = bit_length(n)-1; # 2**e+1    
    if not e&(e-1) :  # e = 2**k
      d = xrange(4*e+1,maxfactor,4*e) if maxfactor else count(4*e+1,4*e);
    else :
      x = (1<<(1<<(bit_length(e&-e)-1)))+1;
      for p in fmerge(factor(x),factor(n//x)) : yield p;
      return;
  for p in d :
    if p*p > n :
      if n > 1 : yield (n,1);
      return;
    c = 0;
    while not n % p :
      n //= p;
      c += 1;
    if c :
      yield (p,c);
      if n > primalitytestlimit and isprime(n) :
        yield (n,1);
        return;
  if n > 1 : yield (n,1);

def unfactor(q) :
  """Given sequence of (base,exponent) pairs, return product"""
  p = 1;
  for (n,c) in q : p *= n**c;
  return p;

def nufactor(n,maxfactor=None) :
  """Return factorization of n so unfactor returns n"""
  if n <= 0 :
    yield (n and -1,1);
  for x in factor(n,maxfactor) : yield x;    # yield from factor(n,maxfactor)
  
def fmerge(*args) :
  """Merge factor generators into a single one"""
  d = dict();
  for a in args :
    try :
      d[a] = next(a);
    except StopIteration :
      pass;
  while d :
    f = sorted(d.items(),key=lambda x:x[1][0]);
    p,k = f[0][1];
    for i,j in enumerate(f[1:],1) :
      if j[1][0] == p :
        k += j[1][1];
      else:
        break;
    else :
      i = len(f);
    yield (p,k);
    for j in xrange(i) :
      x = f[j][0];
      try :
        d[x] = next(x);
      except StopIteration :
        del d[x];
  return;

def mpmul(p,f,g,m=None,c=None) :
  """Return the product of f and g, polynomials over GF(p), modulo polynomial m;
     if c, add c to the constant term of the product."""
  f = lstrip(f);
  g = lstrip(g);
  if m is not None :
    m = lstrip(m);
    if len(m) < 2 :    # constant modulus
      if m : return ();
      raise ZeroDivisionError;
  if not f or not g : return (c,) if c else ();
  fg = (len(f)+len(g)-1)*[0];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] = (fg[i+j]+f[i]*g[j])%p;
  if c : fg[-1] += c;
  return mpmod(p,fg,m) if m else tuple(lstrip(fg));

def lstrip(f) :
  for i,x in enumerate(f) :
    if x : return f[i:] if i else f;
  return ();

def mpadd(p,f,g) :
  """Return the sum of f and g, polynomials over GF(p)"""
  f = lstrip(f);
  g = lstrip(g);
  lf = len(f);
  lg = len(g);
  if lf < lg : lf,lg,f,g = lg,lf,g,f;
  ld = lf-lg;
  s = list(f);
  for i in xrange(lg) :
    s[ld+i] = (s[ld+i]+g[i])%p;
  return tuple(lstrip(s));

def mpsub(p,f,g) :
  """Return the difference of f and g, polynomials over GF(p)"""
  return mpadd(p,f,mpneg(p,g));

def mpneg(p,f) :
  """Return the additive inverse of f, a polynomial over GF(p)"""
  return tuple(-x%p for x in lstrip(f));

def mpmod(p,f,g) :
  """Return f mod g, polynomials over GF(p)"""
  g = lstrip(g);
  if not g : raise ZeroDivisionError;
  r = list(lstrip(f));
  dr = len(r)-1;
  dg = len(g)-1;
  if dr < dg :
    return tuple(r);
  ig = pow(g[0],p-2,p);
  for i in xrange(dr+1-dg) :
    if r[i] :
      q = r[i]*ig%p;
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q*g[j])%p;
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return ();
  return tuple(r[i:]);

def mpdivrem(p,f,g) :
  """Return the quotient and remainder from dividing f by g, polynomials over GF(p)"""
  g = lstrip(g);
  if not g : raise ZeroDivisionError;
  r = list(lstrip(f));
  dr = len(r)-1;
  dg = len(g)-1;
  if dr < dg :
    return (),tuple(r);
  ig = pow(g[0],p-2,p);
  q = [];
  for i in xrange(dr+1-dg) :
    q.append(r[i]*ig%p);
    if q[-1] :
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q[-1]*g[j])%p;
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return tuple(q),();
  return tuple(q),tuple(r[i:]);

def mppow(p,b,e,m=None) :
  """Raise b, a polynomial over GF(p), to the nonnegative integer power e, modulo polynomial m"""
  if m is not None :
    m = lstrip(m);
    if len(m) < 2 :
      if m : return ();
      raise ZeroDivisionError;
  if not e : return one;
  n = 1 << (bit_length(e)-1) >> 1;
  x = b;
  while n :
    x = mpmul(p,x,x,m);
    if e&n :
      x = mpmul(p,x,b,m);
    n >>= 1;
  return x;

def mpgcd(p,f,g) :
  """Return the monic gcd of f and g, all polynomials over GF(p)"""
  f = lstrip(f);
  g = lstrip(g);
  while g :
    f,g = g, mpmod(p,f,g);
  return mpmul(p,f,(pow(f[0],p-2,p),)) if f and f[0] != 1 else f;

def xmpgcd(p,f,g) :
  """Return the monic gcd d of f and g, together with u,v such that d=uf+vg,
all polynomials over GF(p); note that g**-1 mod f = xmpgcd(p,f,g)[2]"""
  u0,v0,u1,v1 = one,(),(),one;
  f = lstrip(f);
  g = lstrip(g);
  while g :
    q,r = mpdivrem(p,f,g);
    f,g = g,r;
    u0,v0,u1,v1 = u1,v1,mpsub(p,u0,mpmul(p,q,u1)),mpsub(p,v0,mpmul(p,q,v1));
  if f and f[0] != 1:
    q = (pow(f[0],p-2,p),);
    f = mpmul(p,f,q);
    u0 = mpmul(p,u0,q);
    v0 = mpmul(p,v0,q);
  return f,u0,v0;

def m2neg(a) :
  """Return the additive inverse of a (which is a), a packed GF(2) polynomial"""
  return a;

def m2add(a,b) :
  """Return the sum (same as difference) of a and b, packed GF(2) polynomials"""
  return a^b;

m2sub = m2add;

def m2mul(a,b,m=0) :
  """Return the product of a and b, packed GF(2) polynomials, mod m"""
  if not a or not b : return 0;
  p = 0;
  if m :
    M = 1<<(bit_length(m)-1);    # hi order bit of m
    g = M^m;
    M >>= 1;
    N = M-1;
    m = M;
    while m :
      p = ((p&N)<<1)^g if p&M else p<<1;
      if b&m : p ^= a;
      m >>= 1;
    return p;
  while b :
    if b&1 : p ^= a;
    b >>= 1;
    a <<= 1;
  return p;

def m2sq(a,m=0) :
  """Return the square of a, a packed GF(2) polynomial, mod m"""
  p = int(bin(a)[2:],4);
  return m2mod(p,m) if m else p;

def m2mod(a,b) :
  """Return a mod b, packed GF(2) polynomials"""
  if not b : raise ZeroDivisionError;
  lb = bit_length(b);
  while True :
    la = bit_length(a);
    if la < lb : break;
    d = la-lb;
    a ^= b<<d;
  return a;

def m2divrem(a,b) :
  """Return the quotient and remainder from dividing a by b, packed GF(2) polynomials"""
  if not b : raise ZeroDivisionError;
  c = 0;
  lb = bit_length(b);
  while True :
    la = bit_length(a);
    if la < lb : break;
    d = la-lb;
    a ^= b<<d;
    c |= 1<<d;
  return c,a;

def m2gcd(a,b) :
  """Return the gcd of a and b, packed GF(2) polynomials"""
  while b :
    a,b = b,m2mod(a,b);
  return a;

def xm2gcd(a,b) :
  """Return the gcd of a and b, together with u,v such that d=uf+vg,
all packed GF(2) polynomials; note that b**-1 mod a = xm2gcd(a,b)[2]"""
  u0,v0,u1,v1 = 1,0,0,1;
  while b :
    q,r = m2divrem(a,b);
    a,b = b,r;
    u0,v0,u1,v1 = u1,v1,u0^m2mul(q,u1),v0^m2mul(q,v1);
  return a,u0,v0;

def m2pow(b,e,m=0) :
  """Raise b, a packed GF(2) polynomial, to the nonnegative integer power e, mod m"""
  if not e : return 1;
  n = 1 << (bit_length(e)-1);
  x = b;
  n >>= 1;
  while n :
    x = m2sq(x,m);
    if e&n :
      x = m2mul(x,b,m);
    n >>= 1;
  return x;

def isirreducible2(p,k=1) :
  """Return True iff p, a packed GF(2) polynomial, is irreducible over GF(2**k)"""
  n = bit_length(p)-1;
  if n <= 1 : return n==1;
  if not (p&1 and bit_count(p)&1) : return False;
  for r in factors(n) :
    if m2gcd(p,m2pow(2,1<<(n//r*k),p)^2) != 1 : return False;
  return not m2mod(m2pow(2,1<<(n*k),p)^2,p);

def isprimitive2(g) :
  """Return True iff packed GF(2) irreducible polynomial g is primitive"""
  if not g&1 : return False;
  n = bit_length(g)-1;
  o = (1<<n)-1;
  for f in ffactors(o) :
    if f==o : break;    # o is prime; g is primitive
    if m2pow(2,o//f,g) == 1 : return False;
  return True;

def mu(n) :
  """Return the Mobius function of n"""
  if not isint(n) or n < 1 :
    raise ValueError('n must be a positive integer');
  if n <= 1 :
    return 1;
  m = 1;
  if not n&1 :
    if not n&2 : return 0;
    n >>= 1;
    m = -1;
  if n > primalitytestlimit and isprime(n) : return -m;
  p = 3;
  while n > 1 :
    if p*p > n :
      return -m;
    if not n % p :
      n //= p;
      if not n % p : return 0;
      m = -m;
      if n > primalitytestlimit and isprime(n) : return -m;
    p += 2;
  return m;

def irreducible_count(q,n) :
  """Return the number of monic irreducible degree n polynomials over GF(q)"""
  if not primepower(q) : raise ValueError('q must be a power of a prime');
  s = 0;
  for d in xrange(1,n+1) :
    if not n%d :
      s += q**d * mu(n//d);
  return s//n;

def irreducibles(q,n) :
  """Return a tuple of all monic irreducible degree n polynomials over GF(q)
  whose coefficients lie in GF(p), where q = p**k, as tuples of integers.
  All monic irreducible degree n polynomials over GF(q): ffpoly.irreducibles"""
  return tuple(irreducibleg(q,n));

def irreducibleg(q,n) :
  """Generate lexicographically as tuples of nonnegative integers < p,
  all monic irreducible degree n polynomials over GF(q)
  whose coefficients lie in GF(p), where q = p**k.
  All monic irreducible degree n polynomials over GF(q): ffpoly.irreducibleg"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p = p[0];
  for i in xrange(p**n) :
    poly = [];
    j = i;
    for k in xrange(n) :
      poly.append(j%p);
      j //= p;
    poly = tuple(reversed(poly));
    if isirreducible(poly,q) : yield one+poly;

def phi(n) :
  """Return the Euler totient function of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    p *= (n-1)*n**(c-1);
  return p;

def sigma(n) :
  """Return the sum of the positive divisors of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    p *= (n**(c+1)-1)//(n-1);
  return p;

def lam(n) :
  """Return the reduced totient function of n"""
  if not n : return 0;
  p = 1;
  for n,c in factor(n) :
    x = (n-1)*n**(c-1) if n&1 or c < 3 else 1<<(c-2);
    p *= x//gcd(x,p);
  return p;

def numdivisors(n) :
  """Return the number of positive divisors of n"""
  if not n: return 0;
  p = 1;
  for n,c in factor(n) :
    p *= c+1;
  return p;

def divisors(n) :
  """Return the positive divisors of n as a generator"""
  if not n : return;
  yield 1;
  f = [];
  t = [];
  for a in factor(n) :
    f.append(a);
    t.append(1);
    z = 0;
    while z < len(f) :
      p = 1;
      for i,x in enumerate(f) :
        p *= x[0]**t[i];
      yield p;
      while z < len(f) :
        t[z] += 1;
        if t[z] <= f[z][1] :
          z = 0;
          break;
        t[z] = 0;
        z += 1;

def getorder(n) :
  """Return a method that returns the multiplicative order of an element mod n
method attributes: modulus = n, maxorder = lam(n)"""
  l = lam(n);
  f = tuple(factors(l));
  def order(x) :
    x = x%n;
    if gcd(x,n) != 1 : return 0;
    o = l;
    for p in f :
      while not o%p :
        if pow(x,o//p,n) != 1 : break;
        o //= p;
    return o;
  order.modulus = n;
  order.maxorder = l;
  return order;
