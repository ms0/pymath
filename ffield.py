""" finite field classes """

__all__ = ['ffield']

import sys

if sys.version_info>(3,) :
  unicode = str;
  xrange = range;
  range = lambda *x: list(xrange(*x));
  isint = lambda x: isinstance(x,int);
  xmap = map;
  map = lambda *x: list(xmap(*x));
else :
  isint = lambda x: isinstance(x,(int,long));
  _xrange = xrange
  def xrange(*a) :    # because builtin xrange has limited range
    try :
      return _xrange(*a);
    except OverflowError :
      return exrange(*a);
  def exrange(*a) :
    try :
      step = a[2];
    except IndexError :
      step = 1;
    try :
      stop = a[1];
      start = a[0];
    except IndexError :
      stop = a[0];
      start = 0;
    while start < stop :
      yield start;
      start += step;

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except Exception :
  import math
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(math.log(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

def bit_count(n) :
  """Return number of 1 bits in |n|"""
  return bin(n).count('1');

# finite field class

import random
random.seed();

from itertools import chain, count
import matrix
from rational import root

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

try :
  from math import gcd
except Exception :
  def gcd(x,y) :
    """Return the [nonnegative] greatest common divisor of x and y"""
    while y :
      x,y = y, x%y;
    return abs(x);

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
  if not isint(n) : return False;
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
plps = matrix.product(lps);   # product of "little" primes

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

def isirreducible(poly,q) :  # missing leading coefficient assumed to be 1
  """Run the deterministic Rabin test to see if poly is irreducible over GF(q);
q must be a positive power of a prime p; poly is represented as a tuple of
integer coefficients interpreted mod p, ending with the constant term, but
without the leading coefficient, which is taken to be 1"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p,k = p;
  n = len(poly);
  if n <= 1 : return True;
  x = (1,0);
  f = (1,)+poly;
  if p == 2 : return isirreducible2(pack(2,f),k);
  for r in factors(n) :
    if len(mpgcd(p,f,mpsub(p,mppow(p,x,q**(n//r),f),x))) != 1 : return False;
  return not mpdivrem(p,mpsub(p,mppow(p,x,q**n,f),x),f)[1];

def factors(n,maxfactor=None) :
  """Return the prime factors of n in increasing order as a generator"""
  for p in factor(n,maxfactor) : yield p[0];

def factor(n,maxfactor=None) :
  """Return prime factorization of n as generator of (prime,exponent) pairs"""
  n = abs(n);
  if n <= 1 :
    return;
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
  """Given sequence of (prime,exponent) pairs, return product"""
  p = 1;
  for (n,c) in q : p *= n**c;
  return p;

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

def pack(p,a) :
  """Return the evaluation at x=p of a, a tuple of coefficients ending with the constant term"""
  x = 0;
  for z in a :
    x *= p;
    x += z;
  return x;

def unpack(p,x) :
  """Return the tuple of coefficients of the polynomial over GF(p) that evaluates to |x| at p"""
  x = abs(x);
  a = [];
  while x :
    a.append(x%p);
    x //= p;
  return tuple(reversed(a));

zits='0123456789abcdefghijklmnopqrstuvwxyz';

def stradix(x,r=16,n=0) :
  """Return a string representing integer x in radix r
     use alphanumeric zits if r < 37, else use dot-separated decimal zits
     if length of string is less than n, pad on left with 0s to length n"""
  a = [];
  while True :
    a.append(x%r);
    x //= r;
    n -= 1;
    if n<=0 and not x: break;
  a.reverse();
  if r > 36 :
    return '.'.join(map(lambda x:'%d'%(x),a));
  return ''.join(map(lambda x: zits[x],a));

def radstix(s,r=None) :
  """Return an integer represented by the string
     If r is not specified, the string must be of the form
       radix_------- where radix is a 1-or-more-digit base ten number and
       each - is an alphanumeric zit; but if radix is > 36, then
       radix_-.-.-.- where each - is a 1-or-more-digit base ten number;
     If r is specified, it is used as the radix, and
     'radix_' may be omitted but is ignored if present"""
  a = s.split('_');
  if r is None :
    if len(a) != 2 :
      raise ValueError('incorrect format');
    r = int(a[0]);
    a = a[1];
  else :
    if not 1 <= len(a) <= 2 :
      raise ValueError('incorrect format');
    a = a[-1];
  if r < 2 :
    raise ValueError('radix must be at least 2');
  x = 0;
  if r > 36 :
    for z in map(int,a.split('.')) :
      if not 0 <= z < r : raise ValueError('non zit encountered');
      x = r*x+z;
  else :
    for c in a :
      try :
        z = zits.index(c);
      except ValueError :
        raise ValueError('non zit encountered');
      x = r*x+z;
  return x;

def __init__(self,x) :
  """Create a finite field element given its polynomial representation, x
The polynomial can be represented as
  a callable, whose value at p gives one of the following
  an integer with absolute value < p**n :
    if nonnegative, x is the value of the polynomial at p
    if negative, -x is the representation of the negative of the field element
  if p <= 36, a string of at most n zits, each having a value < p;
    these values are the polynomial coefficients, ending with the constant;
    the string is stripped and converted to lower case before evaluation;
    zit values are their positions in '0123456789abcdefghijklmnopqrstuvwxyz'
  an iterable of integers, each with absolute value < p
    these (mod p) are the polynomial coefficients, ending with the constant
    the polynomial evaluated at p must be < p**n
Instance variables:
  _p: the characterisitic of the field (inherited from the type)
  _n: the degree of the polynomial modulus (inherited from the type)
  _x: the polynomial representation, evaluated at x=p"""
  p = self._p;
  n = self._n;
  pn = p**n;
  try :
    x = x(p);
  except Exception :
    pass;
  if isint(x) :
    if -pn < x < pn :
      if x < 0 :
        if p == 2 :
          x = -x;
        elif x > -p :
          x += p;
        else :
          x = -x;
          a = [];
          while x :
            a.append(-x%p);
            x //= p;
          for c in reversed(a) :
            x *= p;
            x += c;
      self._x = x;
    else :
      raise ValueError('absolute value must be < %d'%(pn));
  elif isinstance(x,(str,unicode)) :
    if p > 36 :    # string not acceptable if p > 36
      raise TypeError('string not acceptable for p > 36');
    s = x.strip().lower();
    x = 0;
    for c in s :
      try :
        x = x*p + zits[:p].index(c);    # will raise ValueError if illegal
      except ValueError :
        raise ValueError('zits in string must be in "%s"'%(zits[:p]));
      if x > pn :
        raise ValueError('value must be < %d'%(pn));
    self._x = x;
  elif isinstance(type(x),ffield) :
    if x._p != p :
      raise TypeError('ffield element must have same field characteristic');
    if x._x < p or x._n == n :
      self._x = x._x;
    else :
      raise TypeError('ffield element must be in field');
  else :
    try :
      c = iter(x);
    except Exception :
      raise TypeError('uninterpretable arg');
    x = 0;
    for i in c :
      if not isint(i) :
        raise TypeError('iterable elements must be integers');
      if not -p < i < p :
        raise ValueError('absolute value of iterable elements must be < %d)'%(p));
      x *= p
      x += i%p;
      if x >= pn :
        raise ValueError('value must be < %d'%(pn));
    self._x = x;

@property
def element(self) :
  """the field element's polynomial representation evaluated at p"""
  return self._x;

@property
def field_p(self) :
  """the field's characteristic"""
  return self._p;

@property
def field_n(self) :
  """the degree of the field representation's polynomial modulus"""
  return self._n;

@property
def field_poly(self) :
  """the field representation's polynomial modulus minus x**n, evaluated at x=p"""
  return self._poly;

@property
def field_tupoly(self) :
  """the field representation's polynomial modulus minus x**n, as a tuple"""
  return self._tupoly[self._nzi:] if self._nzi else ();

@property
def element_order(self) :
  """The multiplicative order of the field element"""
  o = self._p**self._n-1;
  if self._x <= 1 :
    return self._x;
  for p in factors(o) :
    while not o%p :
      if (self**(o//p))._x != 1 : break;
      o //= p;
  return o;

@property
def field_ftupoly(self) :
  """the field representation's polynomial modulus, as a tuple"""
  return self._tupoly;

@property
def field_nzi(self) :
  """minus the length of tupoly"""
  return self._nzi;

@property
def generates(self) :
  o = self._p**self._n-1;
  if self._x <= 1 :
    return self._x==o;
  for p in factors(o) :
    if (self**(o//p))._x == 1 : return False;
  return True;

def __hash__(self) :
  return hash(self.__class__) ^ hash(self._x);

def __eq__(self,other) :
  """Test if two elements are in the same class and have the same value"""
  return self.__class__ == other.__class__ and self._x == other._x;

def __ne__(self,other) :
  """Test if two elements are in different classes or have different values"""
  return self.__class__ != other.__class__ or self._x != other._x;

__le__ = __ge__ = __eq__;
__lt__ = __gt__ = lambda x,y:False;

def __bool__(self) :
  return self._x != 0;

__nonzero__ = __bool__

def __int__(self) :
  """Return the polynomial representation of the finite field element evaluated at x=p,
a nonnegative integer < p**n; for n=1, it is just the obvious mod p integer"""
  return self._x;

def __str__(self) :
  """Return a string representing the polynomial representation of the finite field element
If n = 1, return the value as a decimal integer, the polynomial evaluated at x=p
Otherwise, return the coefficients in sequence ending with the constant term;
if p <= 36, each coefficient is a zit; else each is a decimal integer, period separated"""
  x = self._x;
  n = self._n;
  p = self._p;
  if n == 1 : return '%d'%(x);
  return stradix(x,p,n);

def __repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
The string begins with the characterisitic of the field as a decimal integer and is followed
by an underscore and the __str__ representation"""
  return str(self._p)+'_'+str(self);

def __add__(self,other) :
  """Return the sum of the two finite field elements; integers are treated mod p"""
  p = self._p;
  n = self._n;
  x = self._x;
  if other.__class__ != self.__class__ :
    if other.__class__.__class__ == ffield and other._p == p :
      if n == 1 :
        return other+x;
      if other._n == 1 :
        other = other._x;
    if isint(other) :
      if p == 2 :
        return self.__class__(x^1) if other&1 else self;
      other %= p;
      return self.__class__(x-x%p+(x+other)%p) if other else self;
    raise TypeError('must be elements of same field');
  y = other._x;
  if not y : return self;
  if p == 2 :
    return self.__class__(x^y);
  if n == 1 :
    return self.__class__((x+y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x+y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return self.__class__(s);

def __pos__(self) :
  """Return the element"""
  return self;

def __neg__(self) :
  """Return the additive inverse of the element"""
  x = self._x;
  if not x : return self;
  p = self._p;
  n = self._n;
  if p == 2 : return self;
  if n == 1 : return self.__class__(-x%p);
  a = [];
  while x :
    a.append(-x%p);
    x //= p;
  for c in reversed(a) :
    x *= p;
    x += c;
  return self.__class__(x);

def __sub__(self,other) :
  """Return the difference of the two finite field elements; integers are treated mod p"""
  p = self._p;
  n = self._n;
  x = self._x;
  if other.__class__ != self.__class__ :
    if other.__class__.__class__ == ffield and other._p == p :
      if n == 1 :
        return x-other;
      if other._n == 1 :
        other = other._x;
    if isint(other) :
      if p == 2 :
        return self.__class__(x^1) if other&1 else self;
      other %= p;
      return self.__class__(x-x%p+(x-other)%p) if other else self;
    else :
      raise TypeError('must be elements of same field');
  y = other._x;
  if not y : return self;
  if p == 2 : return self.__class__(x^y);
  if n == 1 : return self.__class__((x-y)%p);
  a = [];
  for i in xrange(n) :
    a.append((x-y)%p);
    x //= p;
    y //= p;
  s = 0;
  for c in reversed(a) :
    s *= p;
    s += c;
  return self.__class__(s);

def __rsub__(self,y) :
  """Return the difference of the swapped finite field elements; integers  are treated mod p"""
  p = self._p;
  if not isint(y) :
    raise TypeError('must be elements of same field');
  if p == 2 :
    return self.__class__(self._x^1) if y&1 else self;
  y %= p;
  return self.__class__(y)-self if y else -self;

def __div__(self,y) :
  """Return the quotient of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  n = self._n;
  if y.__class__ != self.__class__ :
    if y.__class__.__class__ == ffield and y._p == p :
      if n == 1 :
        return x/y;
      if y._n == 1 :
        y = y._x;
    if isint(y) :
      y %= p;
      if not y : raise ZeroDivisionError;
      if y == 1 : return self;
      d = pow(y,p-2,p);
      a = [];
      for i in xrange(n) :
        a.append(x*d%p);
        x //= p;
      s = 0;
      for c in reversed(a) :
        s *= p;
        s += c;
      return self.__class__(s);
    else : raise TypeError('must be elements of same field');
  yx = y._x;
  if yx < p : return self/yx;
  if p == 2 : return self*y**((1<<n)-2);    # self*y**(p**n-2)
  return self*self.__class__(pack(p,xmpgcd(p,self._tupoly,unpack(p,yx))[2]));


def __rdiv__(self,y) :    # y/self
  """Return y/self; y must be an integer and is interpreted mod p"""
  p = self._p;
  if not isint(y) :
    raise TypeError('must be elements of same field');
  x = self._x;
  if not x : raise ZeroDivisionError;
  y %= p;
  if not y :
    z = 0;
  elif p == 2 :
    return self**-1;
  elif x < p :
    z = y*pow(x,p-2,p)%p;
  else :
    z = 0;
    for i in xmpgcd(p,self._tupoly,unpack(p,x))[2] :
      z = p*z+i*y%p;
  return self.__class__(z);

def __mul__(self,y) :
  """Return the product of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  n = self._n;
  if y.__class__ != self.__class__ :
    if y.__class__.__class__ == ffield and y._p == p :
      if n == 1 :
        return y*x;
      if y._n == 1 :
        y = y._x;
    if isint(y) :
      y %= p;
      if not y : return self.__class__(0);
      if y == 1 : return self;
      a = [];
      for i in xrange(n) :
        a.append(x*y%p);
        x //= p;
      s = 0;
      for c in reversed(a) :
        s *= p;
        s += c;
      return self.__class__(s);
    else : raise TypeError('must be elements of same field');
  if n == 1 :
    return self.__class__(x*y._x%p);
  if p == 2 :
    y = y._x;
    g = self._poly;
    xy = 0;
    M = 1<<(n-1);
    N = M-1
    m = M;
    while m :
      xy = ((xy&N)<<1)^g if xy&M else xy<<1;
      if y&m : xy ^= x;
      m >>= 1;
    return self.__class__(xy);
  return self.__class__(pack(p,mpmul(p,unpack(p,x),unpack(p,y._x),self._tupoly)));

def __pow__(self,e) :
  """Raise the finite field element to the specified power mod p**n-1, 0**0=0"""
  if not isint(e) :
    raise TypeError('power must be integer');
  x = self._x;
  if x <= 1 :
    if x or e > 0 : return self;
    if e : raise ZeroDivisionError;
    return self+1;
  p = self._p;
  n = self._n;
  o = p**n-1;
  e %= o;
  if e == 0:
    x = 1;
  elif e == 1 :
    return self;
  elif x < p :
    x = pow(x,e,p);
  elif p == 2 :
    g = self._poly;
    M = 1<<(n-1);
    N = M-1;
    n = 1<<(bit_length(e)-2);
    b = x;
    while n :
      z = 0;      # compute z = x*x mod g ...
      m = M;
      while m :
        z = ((z&N)<<1)^g if z&M else z<<1; 
        if x&m : z ^= x
        m >>= 1;
      if e&n :
        x = 0;    # compute x = z*b mod g ...
        m = M;
        while m:
          x = ((x&N)<<1)^g if x&M else x<<1;
          if b&m : x ^= z;
          m >>= 1;
      else :
        x = z;
      n >>= 1;
  elif o-e <= o//8 :
    return 1/self**(o-e);
  else :
    x = pack(p,mppow(p,unpack(p,x),e,self._tupoly));
  return self.__class__(x);

def _log(self,base=None,alt=False) :
  """Return the discrete log base base (default: least generator) of self
     if alt, values are signed; always searched by increasing magnitude"""
  x = self._x;
  if x : 
    if base is None :
      base = self.__class__.generator;
    elif not base :
      raise ValueError('bad base');
    q,r = divmod(base.order,self.order);
    if not r :
      if alt :
        for i,g in enumerate(self.__class__.iterpow(base**q,alt),1) :
          if g._x == x : return (-(i>>1) if i&1 else (i>>1))*q;
      else :
        for i,g in enumerate(self.__class__.iterpow(base**q)) :
          if g._x == x : return i*q;
  raise ValueError('not in multiplicative group');  

def _vector(x) :
  """A generator of the coefficients of the polynomial representation"""
  p = x._p;
  n = x._n;
  x = x._x;
  for _ in xrange(n) :
    yield x%p;
    x //= p;

def minpoly(self,m=1) :
  """Return, as a tuple of elements of the subfield GF(self._p**m),
the coefficients, constant term last, of the minimal polynomial of self
over the subfield. Raise an exception if m does not divide self._n.
"""
  n = self._n;
  if m <= 0 or n%m : raise ValueError('m must divide self._n');
  G = self.__class__;
  o = self.order;
  p = self._p;
  G1 = G(1);
  O = p**m-1;    # order of subfield
  if not O%(o or 1) :    # already in subfield
    return (G1,-self);
  d = 1;    # calculate degree of minpoly...
  while (p**(m*d)-1)%o :    # order of element must divide order of subfield
    d += 1;
  if m > 1 :
    # brute force algorithm...
    # ceil(ceil(log(o+1,p))/m) is min possible degree of minpoly
    # n/m is the max possible degree
    G0 = G(0);
    P = [G0]*(n//m) + [G1];    # coeffs of 1, x, x**2, x**3, ... x**(n/m)
    for i in xrange(p,G.__len__()) :  # find generator of superfield of subfield
      g = G(i);
      if not g.order % O: break;
    g **= g.order // O;   # generator of subfield
    P[d] = G1;
    while True :
      # evaluate P(self)
      v = G0;
      for i in xrange(d,0,-1) :
        v = (v+P[i])*self;
      if not O%(v.order or 1) :    # evaluates to element of subfield
        P[0] = -v;
        return tuple(P[d::-1]);
      # try next
      for i in xrange(1,d+1) :
        if P[i] :
          if P[i] == G1 :
            P[i] = G0;
          else :
            P[i] *= g;
            break;
        else:
          P[i] = g;
          break;
      else :
        # d += 1;    # should never happen
        # P[d] = G1;
        raise ValueError('Math failure');
  # get minpoly over GF(p) ...
  X = [];
  x = G1;
  for i in xrange(d) :
    X.append(tuple(map(G,_vector(x))));
    x *= self;
  v = list(_vector(x));    # self**d
  M = matrix.matrix(n,d,list(chain.from_iterable(X))).T;
  if n > d :
    for c in reversed(xrange(n)) :  # eliminate redundant columns from M and v
      N = matrix.matrix(d,len(v)-1,M[:d*c]+M[d*(c+1):]);
      if N.rank == d :
        M = N;
        del v[c];
        if len(v) == d : break;
  v = map(G,v);
  return (G(1),)+tuple(-(v*M.inverse))[::-1];

def _create(p,n,poly,x=None) :
  """Return an ffield instance or, if x present, an instance of an ffield instance"""
  F = ffield(p,n,poly);
  return F if x is None else F(x);

def __reduce__(self) :
  """Return a tuple for pickling"""
  return (_create,(self._p,self._n,self._poly,self._x));

_ffield = {}; # (p,n,poly) -> ffield

class ffield(type) :
  """Class to create finite field class for GF(p**n)
Field elements are represented as polynomials over GF(p) with degree < n.
Arithmetic is done modulo a specified irreducible monic polynomial of degree n.
That polynomial modulus is represented as a tuple of coefficients, length <= n,
constant term last; the coefficient of x**n is elided and assumed to be 1 while
immediately following zero coefficients may be elided as well.
The polynomial is also stored as its value at x=p, again without the x**n term.
The polynomial modulus can be specified in either of those ways.
Instance variables (treat as read-only!):
  _p: characteristic (a prime)
  _n: dimension (giving the field p**n elements)
  _tupoly: the unelided polynomial modulus as a tuple with first element 1
  _poly: an integer giving the value of the elided polynomial at x = __p
  _nzi: minus the length of the tuple representing the elided polynomial modulus
Methods: __new__, __init__, __hash__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
         __len__, __iter__, __getitem__,  __contains__, iterpow, __reduce__
Descriptors: p, n, poly, tupoly, ftupoly, order [of field-{0}], generator [of field-{0}]

Signatures:
  ffield(q) : q = p**n, a prime power; use least irreducible polynomial
  ffield(q,n,poly) : q, a prime; n, a positive int; poly, a la tupoly or poly
  ffield(q,n) : q, a prime; n, a positive int; use least irreducible polynomial
  ffield(q,poly) : q, a prime power; poly, a la tupoly or poly

Each instance of the created type is an element of the finite field:
Instance variable (treat as read-only!):
  _x: the value at _p of the polynomial representing the element

Methods: __init__, __hash__, __repr__, __str__, __int__,
         __pos__, __neg__,
         __bool__, __nonzero__, __eq__, __ne__, __lt__, __gt__, __le__, __ge__
         __add__, __radd__, __sub__, __rsub__,
         __mul__, __rmul__, __div__, __rdiv__, __truediv__, __rtruediv__,
         __pow__, log, minpoly,
         __reduce__
Descriptors: p, n, poly, tupoly, ftupoly, x,
             order [of element], generator [True if element generates]
"""

  def __new__(cls,q,*args,**kwargs) :
    q = primepower(q);
    if not q :
      raise ValueError('Not prime power');
    p,n = q;
    poly = kwargs.pop('poly',None);
    dn = kwargs.pop('n',None);
    if dn != None :
      if n != 1 :
        raise ValueError('n specified for prime power');
      n = dn;
    if len(kwargs) :
      raise TypeError('Allowed keywords: n poly')
    if args :
      if len(args) == 1 :
        if (dn or n != 1) and poly != None :
          raise TypeError('too many arguments');
        x = args[0]
        if n == 1 and isint(x) and x :
          n = x;
        elif poly == None :
          poly = x;
        else :
          raise TypeError('too many arguments');
      elif len(args) == 2 :
        if n != 1 or poly != None :
          raise TypeError('too many arguments');
        n,poly = args;
      else :
        raise TypeError('too many arguments');
    poly = poly or 0;
    if  n < 1 or not isint(n) :
      raise ValueError('Bad power');
    q = p**n;
    if not poly and n > 1:    # pick least irreducible poly
      d = p if p==2 or (p-1)%matrix.product(factors(n),1 if n&3 else 2) else 0;
      for poly in xrange(q+d+1,q+q) :
        if isirreducible(unpack(p,poly)[1:],p) : break;
      poly -= q;
    if isint(poly) :
      if not 0 <= poly < q : raise ValueError('Bad poly');
    elif isinstance(poly,tuple) and len(poly) <= n :
      tupoly = poly;
      poly = 0;
      for c in tupoly :
        if not (isint(c) and 0 <= c < p) :
          raise ValueError('Bad poly');
        poly = p*poly + c;
    else : raise ValueError('Bad poly');
    tupoly = unpack(p,poly);
    _nzi = -len(tupoly);
    _tupoly = (1,)+(n+_nzi)*(0,)+tupoly;
    if not isirreducible(_tupoly[1:],p) :
      raise ValueError('Composite poly');
    x = (p,n,poly);
    try :
      return _ffield[x];
    except Exception :
      pass;
    d = dict(p=field_p,n=field_n,poly=field_poly,x=element,
             minpoly = minpoly,
             tupoly = field_tupoly,
             ftupoly = field_ftupoly,
             order = element_order,
             generator = generates,
             _p=p,_n=n,_poly=poly,_tupoly=_tupoly,_nzi=_nzi,
             __init__=__init__,
             __repr__=__repr__,
             __str__=__str__,
             __int__=__int__,
             __hash__=__hash__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __bool__ = __bool__,
             __nonzero__=__nonzero__,
             __neg__=__neg__,
             __pos__=__pos__,
             __add__=__add__,
             __radd__=__add__,
             __sub__=__sub__,
             __rsub__=__rsub__,
             __mul__=__mul__,
             __rmul__=__mul__,
             __div__=__div__,
             __truediv__=__div__,
             __rdiv__=__rdiv__,
             __rtruediv__=__rdiv__,
             __pow__=__pow__,
             log = _log,
             __reduce__=__reduce__,
            );

    name = ('GF%d'%(p) if n == 1 and not tupoly else
            'GF%d_%s'%(p,zits[poly] if p <= 36 else str(poly)) if n == 1 else
            'GF%d_%d_%s'%(p,n,''.join([zits[c] for c in tupoly])) if p <= 36 else
            'GF%d_%d_%s'%(p,n,'_'.join(['%d'%(c) for c in tupoly])));
    _ffield[x] = f = type.__new__(cls,name,(),d);
    return f;

  def __init__(self,*args,**kwargs) :
    return;

  def __reduce__(self) :
    """Return a tuple for pickling"""
    return (_create,(self._p,self._n,self._poly));

  def __hash__(self) :
    return hash(self.__class__)^hash('%s:%s'%(self._p**self._n,self._poly));

  def __eq__(self,other) :
    return self.__class__==other.__class__ and self._p==other._p and self._n==other._n and self._poly==other._poly;
  
  def __ne__(self,other) :
    return not self==other;

  __le__ = __eq__;
  __ge__ = __eq__;
  __lt__ = __lt__;
  __gt__ = __gt__;

  def __len__(self) :
    """Return p**n, the size of the field"""
    return self._p**self._n;

  def __iter__(self) :
    """Return an iterator for the elements of the field"""
    return (self(x) for x in xrange(self._p**self._n));

  def __getitem__(self,key) :
    """Return tuple(self)[key]"""
    if isint(key) :
      pn = self.__len__();
      if -pn <= key < pn :
        return self(key%pn);
      raise IndexError('index out of range');
    elif isinstance(key,slice) :
      return tuple(self(i) for i in range(*key.indices(self.__len__())));
    raise IndexError('index must be integer or slice');

  def __contains__(self,x) :
    """Return True iff x is an element of the field"""
    return (isinstance(x,self) or isinstance(x,int) and abs(x) < self._p or
            isinstance(x.__class__,ffield) and x._p == self._p and x._x < x._p);

  def iterpow(self,x=0,alt=False) :
    """Return an iterator of the powers of x, or powers of smallest generator
       power sequence: 0,1,2,..., or, if alt, 0,1,-1,2,-2,..."""
    if not x :
      x = self.generator;
    if alt :
      def g(f) :
        e = x;
        y = 1/x;
        while True :
          yield f;
          if e._x == f._x : break;
          yield e;
          e *= x;
          if e._x == f._x : break;
          f *= y;
    else :
      def g(e) :
        while True :
          yield e;
          e *= x;
          if e._x <= 1 : break;
    return g(self(1));

  p = field_p;
  n = field_n;
  poly = field_poly;
  tupoly = field_tupoly;
  ftupoly = field_ftupoly;

  @property
  def order(self) :
    """p**n-1, the multiplicative order of the field"""
    return self._p**self._n-1;

  @property
  def generator(self) :
    """the "smallest" generator of the field"""
    try :
      return self.__generator;
    except AttributeError :
      for g in self :
        if g.generator :
          self.__generator = g;
          return g;

  def foo(self,foo=None) :
    raise AttributeError("type object '%s' has no Attribute 'x'"%(self.__name__));

  x = property(foo,foo,foo);
  del foo;


# how do we display an instance ?
# possibility 0:
#   non-negative integer: coeff(g**0)+p*(coeff(g**1)+p*(...coeff(g**(n-1))...))
# possibility 1:
#  if n = 1, just the non-negative integer, in decimal
#  if n > 1, a tuple of non-negative integers: coeffs of g**(n-1), ...g**1, g**0
# possibility 1r:
#  if n > 1, a tuple of non-negative integers: coeffs of g**0, g**1, ...g**(n-1)
# possibility 2:
#  if p <= 36, base p representation of possibility 0
#  else, possibility 0
# possibility 3:
#  if p == 2, hexadecimal of possibility 0
#  else, possibility 2

# mul is hardest
# pow exponent must be integer
# div (all versions) is same, and uses pow(-1) = pow(p**n-2); divide by zero raises Error
# no rdiv? but rmul

# NOTE, if polynomial is not irreducible, the class is still a ring.
# We can still multiply polynomials mod poly
# We can still perform gcd.

# modular polynomial functions
# polynomials represented as tuples of mod p integers, hi to lo
# note 1/x = x**(p-2)

def mpmul(p,f,g,m=None) :
  """Return the product of f and g, polynomials over GF(p), modulo polynomial m"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  if not f or not g : return ();
  fg = (len(f)+len(g)-1)*[0];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] = (fg[i+j]+f[i]*g[j])%p;
  while fg and not fg[0] : fg = fg[1:];
  return tuple(fg) if not m else mpdivrem(p,fg,m)[1];

def mpadd(p,f,g) :
  """Return the sum of f and g, polynomials over GF(p)"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  lf = len(f);
  lg = len(g);
  if lf < lg : lf,lg,f,g = lg,lf,g,f;
  ld = lf-lg;
  s = list(f);
  for i in xrange(lg) :
    s[ld+i] = (s[ld+i]+g[i])%p;
  while s and not s[0] : s = s[1:];
  return tuple(s);

def mpsub(p,f,g) :
  """Return the difference of f and g, polynomials over GF(p)"""
  n = mpneg(p,g);
  return mpadd(p,f,n)

def mpneg(p,f) :
  """Return the additive inverse of f, a polynomial over GF(p)"""
  while f and not f[0] : f = f[1:];
  n = [];
  for x in f :
    n.append(-x%p);
  return tuple(n);

def mpdivrem(p,f,g) :
  """Return the quotient and remainder from dividing f by g, polynomials over GF(p)"""
  r = list(f);
  while r and not r[0] : r = r[1:];
  while g and not g[0] : g = g[1:];
  if not g : raise ZeroDivisionError;
  dr = len(r)-1;
  dg = len(g)-1;
  q = [];
  for i in xrange(dr-dg+1) :
    q.append(r[i]*pow(g[0],p-2,p)%p);
    for j in xrange(dg+1) :
      r[i+j] = (r[i+j]-q[-1]*g[j])%p;
  while r and not r[0] : r = r[1:];
  return tuple(q),tuple(r);

def mppow(p,b,e,m=None) :
  """Raise b, a polynomial over GF(p), to the nonnegative integer power e, modulo polynomial m"""
  if not e : return (1,);
  n = 1 << (bit_length(e)-1);
  x = b;
  n >>= 1;
  while n :
    x = mpmul(p,x,x,m);
    if e&n :
      x = mpmul(p,x,b,m);
    n >>= 1;
  return x;

def mpgcd(p,f,g) :
  """Return the monic gcd of f and g, all polynomials over GF(p)"""
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
  while g :
    f,g = g, mpdivrem(p,f,g)[1];
  return mpmul(p,f,(pow(f[0],p-2,p),)) if f and f[0] != 1 else f;

def xmpgcd(p,f,g) :
  """Return the monic gcd d of f and g, together with u,v such that d=uf+vg,
all polynomials over GF(p); note that g**-1 mod f = xmpgcd(p,f,g)[2]"""
  u0,v0,u1,v1 = (1,),(),(),(1,);
  while f and not f[0] : f = f[1:];
  while g and not g[0] : g = g[1:];
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
  p = 0;
  if not a or not b : return 0;
  while b :
    if b&1 : p ^= a;
    b >>= 1;
    a <<= 1;
  return m2divrem(p,m)[1] if m else p;

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
    a,b = b,m2divrem(a,b)[1];
  return a;

def m2pow(b,e,m=0) :
  """Raise b, a packed GF(2) polynomial, to the nonnegative integer power e, mod m"""
  if not e : return 1;
  n = 1 << (bit_length(e)-1);
  x = b;
  n >>= 1;
  while n :
    x = m2mul(x,x,m);
    if e&n :
      x = m2mul(x,b,m);
    n >>= 1;
  return x;

def isirreducible2(p,k=1) :
  """Return True iff p, a packed GF(2) polynomial, is irreducible over GF(2**k)"""
  n = bit_length(p)-1;
  if n <= 1 : return True;
  if not (p&1 and bit_count(p)&1) : return False;
  for r in factors(n) :
    if m2gcd(p,m2pow(2,1<<(n//r*k),p)^2) != 1 : return False;
  return not m2divrem(m2pow(2,1<<(n*k),p)^2,p)[1];

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
  All monic irreducible degree n polynomials over GF(q): poly.irreducibles"""
  return tuple(irreducibleg(q,n));

def irreducibleg(q,n) :
  """Generate all monic irreducible degree n polynomials over GF(q)
  whose coefficients lie in GF(p), where q = p**k, as tuples of integers.
  All monic irreducible degree n polynomials over GF(q): poly.irreducibleg"""
  p = primepower(q);
  if not p : raise ValueError('q must be a power of a prime');
  p = p[0];
  for i in xrange(p**n) :
    poly = [];
    j = i;
    for k in xrange(n) :
      poly.append(j%p);
      j //= p;
    poly = tuple(poly);
    if isirreducible(poly,q) : yield (1,)+poly;

def phi(n) :
  """Return the Euler totient function of n"""
  p = 1;
  for n,c in factor(n) :
    p *= (n-1)*n**(c-1);
  return p;

def sigma(n) :
  """Return the sum of the positive divisors of n"""
  p = 1;
  for n,c in factor(n) :
    p *= (n**(c+1)-1)//(n-1);
  return p;

def lam(n) :
  """Return the reduced totient function of n"""
  p = 1;
  for n,c in factor(n) :
    x = (n-1)*n**(c-1) if n&1 or c < 3 else 1<<(c-2);
    p *= x//gcd(x,p);
  return p;

def numdivisors(n) :
  """Return the number of positive divisors of n"""
  p = 1;
  for n,c in factor(n) :
    p *= c+1;
  return p;

def divisors(n) :
  """Return the positive divisors of n as a generator"""
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

def lcm(x,y) :
  """Return the [positive] least common multiple of x and y"""
  return abs(x//(gcd(x,y) or 1)*y);

def lcma(*args) :
  """Return the [positive] least common multiple of all the arguments"""
  m = 1;
  for a in args :
    try :
      m *= a//(gcd(m,a) or 1);
    except Exception :
      for i in a :
        m *= i//(gcd(m,i) or 1);
  return abs(m);

def gcda(*args) :
  """Return the [nonnegative] greatest common divisor of all the arguments"""
  d = 0;
  for a in args :
    try :
      d = gcd(d,a);
    except Exception :
      for i in a :
        d = gcd(d,i);
  return d;

def getorder(n) :
  """Return a method that returns the multiplicative order of an element mod n"""
  l = lam(n);
  f = tuple(factors(l));
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
  return order;
