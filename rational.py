# class rational, implementing Q, the field of rational numbers

from __future__ import division

import sys

from math import floor, log as mathlog, isinf, isnan, copysign as mathcopysign
from itertools import chain, count

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,rational,xrational));

else :

  xrange = range;

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,rational,xrational));

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except :
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(mathlog(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

inf = float('inf');
nan = float('nan');
inf_i = complex('infj');
nan_i = complex('nanj');

def sgn(x) :
  """Return the sign of x as an integer: -1, 0, or +1"""
  return -1 if x < 0 else 1 if x else 0;

def gcd(x,y) :
  """Return the [nonnegative] greatest common divisor of x and y"""
  while y :
    x,y = y, x%y;
  return abs(x);

def root(a,n) :
  """Return the nth root of a, where a and n are positive integers"""
  l = mathlog(a,2)/n;
  if l < 1 : return 1;
  try :
    r = int(round(2**l));
  except :    # too big
    il = int(l)-52;
    fl = l - il;
    r = int(round(2**fl))<<52;
  while True :
    if r**n == a : return r;
    ro = r;
    r = ((n-1)*r + a//r**(n-1))//n;
    if -1 <= ro-r <= 1 :
      return ro if abs(a-ro**n) < abs(a-r**n) else r;

class rational(object) :
  """Rational number class
Instance variables:
  a or numerator: the numerator, an integer
  b or denominator: the denominator, a positive integer
  Note that gcd(a,b) == 1.
Methods:
  __new__, __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__,
  __int__, __float__, __round__, __ceil__, __floor__, __trunc__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, exp, cf, approximate"""

  def __new__(cls,a,b=1) :
    """Create a rational number equal to a/b; attempting b=0 raises ZeroDivisionError
If a is a float or rational (and b==1), return the simplest possible rational
If a is a nonempty list or tuple of integers (and b==1),
 they are interpreted as the terms of a regular continued fraction"""
    if not isint(a) or not isint(b) :
      if b == 1 :
        if isinstance(a,(rational,xrational)) :
          return a if a.imag else a.real;
        elif a and isinstance(a,(tuple,list)) :
          m0,m1,n0,n1 = 0,1,1,0;
          for i in a :
            if not isrational(i) : raise TypeError('cf must be rational');
            if i <= 0 and n1 : raise TypeError('cf terms beyond first must be positive');
            m0,m1,n0,n1 = n0,n1,m0+i*n0,m1+i*n1;
          if isint(n0) and isint(n1) :
            a,b = int(n0),int(n1)
          else :
            return n0/n1;
        elif a.imag :
          return xrational(a);
        elif isinstance(a.real,float) and not isinf(a.real) and not isnan(a.real) :
          a = a.real;
          self = super(rational,cls).__new__(cls);
          x = a;
          m0,m1,n0,n1 = 0,1,1,0;
          for i in xrange(64) :
            ix = floor(x);
            fx = x - ix;        
            iix = int(ix);
            m0,m1,n0,n1 = n0,n1,m0+iix*n0,m1+iix*n1;
            if fx == 0 or n0/n1 == a : break;
            x = 1/fx;
          a,b = int(n0),int(n1);
        else :
          raise TypeError('arg must be a number or a nonempty list or tuple of cf terms')
      else :
        raise TypeError('numerator and denominator must be integers');
    else :
      if b < 0 : a,b = -a,-b;
      if not b : raise ZeroDivisionError;
      g = gcd(a,b);
      a = int(a//g);
      b = int(b//g);
    if not a :
      try :
        return _0;
      except :
        pass;    # happens exactly once!
    self = super(rational,cls).__new__(cls);
    self._a,self._b = a,b;
    return self;

  def __init__(self,a,b=1) :
    return;

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self._a,self._b) if self._b != 1 else '%d'%(self._a);

  def __repr__(self) :
    """Return a string showing the rational number as it could be input"""
    return 'rational(%d,%d)'%(self._a,self._b) if self._b != 1 else 'rational(%d)'%(self._a);

  def __hash__(self) :
    """Return a hash for the rational number; if an integer, use that integer's hash"""
    try :
      return hash(self._a) if self._b == 1 else hash(self._a/self._b);
    except :
      return hash(self.cf());

  def __getattr__(self,name) :
    if name in ('a','numerator') :
      return self._a;
    if name in ('b','denominator') :
      return self._b;
    if name == 'real' :
      return self;
    if name == 'imag' :
      return _0;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __lt__(self,other) :
    """Return True iff self < other """
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a < self._b*other;
      if isinstance(other,float) :
        if isnan(other) :
          return False;
        if isinf(other) :
          return other > 0;
        return self < self.__class__(other);
      return NotImplemented;
    return self._a*other._b < self._b*other._a;

  def __le__(self,other) :
    """Return True iff self <= other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a <= self._b*other;
      if isinstance(other,float) :
        if isnan(other) :
          return False;
        if isinf(other) :
          return other > 0;
        return self <= self.__class__(other);
      return NotImplemented;
    return self._a*other._b <= self._b*other._a;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a == self._b*other;
      if isinstance(other,float) :
        return not isinf(other) and not isnan(other) and self == self.__class__(other);
      return NotImplemented;
    return self._a*other._b == self._b*other._a;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a != self._b*other;
      if isinstance(other,float) :
        return not isnan(other) and (isinf(other) or self != self.__class__(other));
      return NotImplemented;
    return self._a*other._b != self._b*other._a;

  def __ge__(self,other) :
    """Return True iff self >= other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a >= self._b*other;
      if isinstance(other,float) :
        if isnan(other) :
          return False;
        if isinf(other) :
          return other < 0;
        return self >= self.__class__(other);
      return NotImplemented;
    return self._a*other._b >= self._b*other._a;

  def __gt__(self,other) :
    """Return True iff self > other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a > self._b*other;
      if isinstance(other,float) :
        if isnan(other) :
          return False;
        if isinf(other) :
          return other < 0;
        return self > self.__class__(other);
      else :
        return NotImplemented;
    return self._a*other._b > self._b*other._a;

  def __bool__(self) :
    """Return True iff self != 0"""
    return self._a != 0;

  __nonzero__ = __bool__

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return self.__class__(-self._a,self._b) if self._a else self;

  def __abs__(self) :
    """Return |self|"""
    return self.__class__(-self._a,self._b) if self._a < 0 else self;

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      if other.imag :
        return xrational(self)+other;
      try :
        return self+self.__class__(other);
      except :
        return other.__class__(self)+other;
    return self.__class__(self._a*other._b+other._a*self._b,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,complex) :
        return xrational(self)-other;
      try :
        return self-self.__class__(other);
      except :
        return other.__class__(self)-other;
    return self.__class__(self._a*other._b-other._a*self._b,self._b*other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    if isinstance(other,complex) :
      return other-xrational(self);
    try :
      return self.__class__(other)-self;
    except :
      return other-other.__class__(self);

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a*other,self._b);
      if isinstance(other,complex) :
        return xrational(self)*other;
      try :
        return self*self.__class__(other);
      except :
        return other.__class__(self)*other;
    return self.__class__(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a,other*self._b);
      if isinstance(other,complex) :
        return xrational(self)/other;
      try :
        return self/self.__class__(other);
      except :
        return other.__class__(self)/other;
    return self.__class__(self._a*other._b,self._b*other._a);

  def __rtruediv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(other*self._b,self._a);
      if isinstance(other,complex) :
        return other/xrational(self);
      try :
        return self.__class__(other)/self;
      except :
        return other/other.__class__(self);
    return self.__class__(self._b*other._a,self._a*other._b);

  __div__ = __truediv__
  __rdiv__ = __rtruediv__

  def __floordiv__(self,other) :
    """Return the floor of the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a//(self._b*other));
      if isinstance(other,complex) :
        return xrational(self)//other;
      try :
        return self//self.__class__(other);
      except :
        return other.__class__(self)//other;
    return self.__class__((self._a*other._b)//(self._b*other._a));

  def __rfloordiv__(self,other) :
    """Return the floor of the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__((self._b*other)//self._a);
      if isinstance(other,complex) :
        return other//xrational(self);
      try :
        return self.__class__(other)//self;
      except :
        return other//other.__class__(self);
    return self.__class__((self._b*other._a)//(self._a*other._b));

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    return self - self//other*other;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return other - other//self*self;

  def __divmod__(self,other) :
    """Return quotient and remainder"""
    q = self//other;
    return (q, self-q*other);

  def __rdivmod__(self,other) :
    """Return quotient and remainder"""
    q = other//self;
    return (q, other-q*self);

  def __pow__(self,other) :
    """Return a number raised to a power; integer powers give exact answer"""
    if isinstance(other,(complex,xrational)) :
      if other.imag :
        try :
          return xrational(self)**other;
        except :
          return exp(other*self.log());
      other = other.real;
    if not self._a :
      if other < 0 :
        raise ZeroDivisionError;
      else :
        return self if other else _1;
    if isinstance(other,float) :
      if isnan(other) : return nan;
      if isinf(other) :
        b=abs(self);
        return _1 if b == 1 else _0 if (b < 1) == (other > 0) else inf;
      other = self.__class__(other);
    if isinstance(other,self.__class__) and other._b == 1 :
      other = other._a;
    if isint(other) :
      if other < 0 :
        return self.__class__(self._b**-other,self._a**-other);
      return self.__class__(self._a**other,self._b**other);
    if not isinstance(other,self.__class__) :
      raise TypeError('exponent must be a number');
    # rational (but not integral) power
    if other._a < 0 :
      if self._a < 0 :
        a,b,c = -self._b, -self._a, -other._a;
      else :
        a,b,c = self._b, self._a, -other._a;
    elif other._a :
      a,b,c = self._a, self._b, other._a;
    d = other._b;
    s = 1;    # tentative sign of result
    if a < 0 :
      if not d&1 :
        return xrational(self)**other;    # even root of negative number
      if c&1 :
        s = -1;
      a = -a;
    # result should be s*a**(c/d) / b**(c/d)
    q,r = divmod(c,d);
    if 2*r > d :
      q += 1;
      r -= d;
    ac,bc = s*a**q,b**q;    # to integer power
    if r < 0 : a,b,r = b,a,-r;
    # want (a/b)**(r/d) * ac/bc
    # first see if a and/or b has an integer root
    ra = root(a,d);
    rb = root(b,d);
    pa = ra**d == a;  # a has an exact root?
    pb = rb**d == b;  # b has an exact root?
    if pa and pb :
      return self.__class__(ra**r*ac,rb**r*bc);    # exact result
    return _exp(self.__class__(a,b).log()*r/d)*ac/bc;

  def __rpow__(self,other) :
    try :
      return self.__class__(other)**self;
    except :
      if isinstance(other,(float,complex)) :
        if self._b == 1 :    # integer power
          n = self._a;
          if n == 1 : return other;
          if n == 0 : return _1;
          if not (isinf(other.real) or isinf(other.imag)) : return nan;
          if n < 0 : return _0;
          if not other.imag :    # pure real +-inf
            return inf if other.real > 0 or not n&1 else -inf;
          if not other.real :    # pure imag +-inf
            return complex(0 if not n&1 else inf if n&2 else -inf,
                           0 if n&1 else (1-(n&2))*other.imag);
          return nan;
        if not (isinf(other.real) or isinf(other.imag)) : return nan;
        if isinf(other.real) and not other.imag :
          return other.real if self > 0 else _0;
        return _0 if self < 0 else nan;
      return other**other.__class__(self);

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return self.__class__(self._a<<other,self._b) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return self.__class__(self._a,self._b<<other) if other >= 0 else self<<-other;

  def __float__(self) :
    """Return a floating point approximation to the number"""
    try :
      return self._a/self._b;
    except OverflowError :
      return sgn(self)*inf;

  def __int__(self) :
    """Return the integer part of the number"""
    return int(-(-self._a//self._b) if self._a < 0 else self._a//self._b);

  __trunc__ = __int__

  def __floor__(self) :
    """Return the floor of the number"""
    return int(self._a//self._b);

  def __ceil__(self) :
    """Return the ceil of the number"""
    return int(-(-self._a//self._b));

  def __round__(self,n=0,base=10) :
    """Return the round of the number"""
    if not isint(n) :
      raise TypeError('n must be an integer');
    if not isint(base) or base < 2 :
      raise ValueError('base must be an integer > 1');
    if not n : return -int(_half-self) if self._a < 0 else int(_half+self);
    base2absn = base**abs(n);
    return ((self.__class__(int((self/base2absn - _half)*base2absn)) if self._a < 0 else
             self.__class__(int((self/base2absn + _half)*base2absn))) if n < 0 else
            self.__class__(-int(_half - self*base2absn),base2absn) if self._a < 0 else
            self.__class__(int(_half + self*base2absn),base2absn));

  def tonx(self,n,base=10) :
    """Return (0,0) if self == 0; else
Return (t,x) with base**(n-1) <= |t| < base**n and |t-self/base**x| <= 1/2"""
    if not (isint(n) and n > 0) :
      raise ValueError('n must be a positive integer');
    if not isint(base) or base < 2 :
      raise ValueError('base must be an integer > 1');
    if not self :
      return (0,0);
    s = abs(self);
    x = int(s.log(base));
    base = rational(base);
    while base**x > s :
      x -= 1;
    while base**(x+1) <= s :
      x += 1;
    t = int(s*base**(n-x-1)+_half);
    base = int(base);
    if t >= base**n :
      t //= base;
      x += 1;
    return (sgn(self)*t,x+1-n);

  def bstr(self,n=5,base=10) :
    """Return an n-digit string representation of self in the specified base;
if the base is not ten, it is included as a decimal number followed by a number sign;
a following << indicates multiplication by the indicated power of the base;
a following >> indicates division by the indicated power of the base"""
    if not (isint(n) and n > 0) :
      raise ValueError('n must be a positive integer');
    if not (isint(base) and 2 <= base <= 36) :
      raise ValueError('base must be an integer in [2,36]')
    if not self : return '0';
    t,x = self.tonx(n,base);
    t = abs(t);
    s = [];
    while t :
      s.append('0123456789abcdefghijklmnopqrstuvwxyz'[t%base]);
      t //= base;
    s = ''.join(s[::-1]);
    return ('-' if self < 0 else '') + (str(base)+'#' if base != 10 else '') + ( 
      s + '<<' + str(x) if x > 0 else
      '.' + s + '>>' + str(-x-len(s)) if -x > len(s) else
      s[:len(s)+x] + ('.' + s[len(s)+x:] if x else ''));

  def arg(self) :
    """Return 0"""
    return _0;

  def log(self,base=None) :
    """Return the log of the number as a rational if finite, else as +-inf"""
    base = self.__class__(base) if base != None else e;
    if base <= 0 or base == 1 : raise ValueError('bad base');
    if not self._a : return inf if base < 1 else -inf;
    d = _ln(base);
    return xrational(_ln(-self)/d,pi/d) if self < 0 else _ln(self)/d;

  def exp(self) :
    """Return exp(self) as a rational"""
    return _exp(self);

  def cf(self) :
    """Return a tuple of the terms of the regular continued fraction for the number"""
    l = [];
    a,b = self._a,self._b;
    while b :
      q = int(a//b);    # turn long into int if possible
      l.append(q);
      a,b = b,int(a-q*b);
    return tuple(l);

  def approximate(self,accuracy=None) :
    """If accuracy is unspecified, or self is an integer, return self; else
If self is negative, approximate -self and return the negative; else
If self < 1, approximate 1/self and return the inverse; else
Return x with least denominator such that |(1-x/self)*accuracy| <= 1"""
    if accuracy == None : return self;
    a,b = self._a,self._b;
    if b == 1 : return self;
    s = sgn(a);    # make sure symmetric over negation
    a *= s;
    if a < b : return 1/(1/self).approximate(accuracy); # make sure symmetric over inversion
    za,zb = a,b;
    m0,m1,n0,n1 = 0,1,1,0;
    while b :
      q = a//b;
      o0,o1 = m0+q*n0,m1+q*n1;    # fully-included term
      if n1 :
        #if abs((z-self.__class__(o0,o1))/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,o0,o1) :
          n = (q+1)//2;    # min possible term
          x = q;           # max possible term
          while True :
            i = (n+x)//2;
            p0,p1 = m0+i*n0,m1+i*n1;
            #r = self.__class__(p0,p1);
            #if abs((z-r)/z*accuracy) > 1 :
            if not _checkaccuracy(accuracy,za,zb,p0,p1) :
              n = i+1;
            else :
              x = i;
              if x == n :
                return self.__class__(s*p0,p1);
      else :
        r = q + (q*(q+1)*zb*zb < za*za);
        #if abs((z-r)/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,r,1) :
          return self.__class__(r*s);
      m0,m1,n0,n1 = n0,n1,o0,o1;
      a,b = b, a-q*b;
    return self;

class xrational(object) :
  """Complex Rational number class
Instance variables:
  real: the real part, a rational
  imag: the imaginary part, a rational
Methods:
  __new__, __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
   __pos__, __neg__, __abs__, __invert__, conjugate,
  __float__, __complex__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, exp, arg, approximate"""

  def __new__(cls,real,imag=0) :
    """Create a complex number equal to real+imag*i; real and imag are converted to rational
If real is complex or xrational (and imag==0), return the corresponding xrational"""
    if imag == 0 :
      if isinstance(real,xrational) : return real;
      if isinstance(real,complex) :
        real,imag = real.real, real.imag;
    try :
      if real.imag or imag.imag : raise TypeError;
      real = rational(real);
      imag = rational(imag);
    except :
      raise TypeError('args must be convertible to rationals');
    self = super(xrational,cls).__new__(cls);
    self._a,self._b = real,imag;
    return self;

  def __init__(self,real,imag=0) :
    return;

  def __str__(self) :
    """Return a string showing the complex rational number"""
    return '%s%s%si'%(self._a,
                      '+' if self._b > 0 else '',
                      self._b) if self._b else '%s'%(self._a);

  def __repr__(self) :
    """Return a string showing the rational number as it could be input"""
    return 'xrational(%s)'%(str(self));

  def __hash__(self) :
    """Return a hash for the xrational number; if an integer, use that integer's hash"""
    try :
      return hash(complex(self._a,self._b));
    except :
      return hash((self._a,self._b));

  def __getattr__(self,name) :
    if name == 'real' :
      return self._a;
    if name == 'imag' :
      return self._b;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __eq__(self,other) :
    """Return True iff self == other"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        return NotImplemented;
    return self._a == other._a and self._b == other._b;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
        if not isinstance(other,self.__class__) : raise NotImplemented;
      except :
        return NotImplemented;
    return self._a != other._a or self._b != other._b;

  def __lt__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a < other;

  def __le__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a <= other;

  def __gt__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a > other;

  def __ge__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a >= other;

  def __bool__(self) :
    """Return True iff self != 0"""
    return bool(self._a) or bool(self._b);

  __nonzero__ = __bool__

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return self.__class__(-self._a,-self._b);

  def __invert__(self) :
    """Return complex conjugate of self"""
    return self.__class__(self._a,-self._b);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self._a**2+self._b**2)**_half;

  def __float__(self) :
    """Return a floating point approximation to the number if real"""
    if self._b : raise TypeError('complex');
    return float(self._a);

  def __complex__(self) :
    """Return a floating point [i.e., complex] approximation to the number"""
    return complex(self._a,self._b);

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return complex(self._a+other.real,self._b+other.imag);
        return other.__class__(self) + other;
    return self.__class__(self._a+other._a,self._b+other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return complex(self._a-other.real,self._b-other.imag);
        return other.__class__(self) - other;
    return self.__class__(self._a-other._a,self._b-other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      return self.__class__(other)-self;
    except :
      if isinstance(other,(float,complex)) :
        return complex(other.real-self._a,other.imag-self._b);
      return other - other.__class__(self);

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return (complex(self._a*other.real,self._a*other.imag) if not self._b else
                  complex(-self._b*other.imag, self._b*other.real) if not self._a else
                  complex(self._a*other.real-self._b*other.imag,self._a*other.imag+self._b*other.real));
        return other.__class__(self)*other;
    return self.__class__(self._a*other._a-self._b*other._b,self._a*other._b+self._b*other._a);

  __rmul__ = __mul__

  def __div__(self,other) :
    """Return the quotient of the two numbers"""
    if not other :
      raise ZeroDivisionError;
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          other = complex(other);
        return other.__class__(self)/other;
    d = other._a**2 + other._b**2;
    return self.__class__((self._a*other._a+self._b*other._b)/d,(self._b*other._a-self._a*other._b)/d);

  def __rdiv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return (complex(other.real/self._a, other.imag/self._a) if not self._b else
                  complex(other.imag/self._b, -other.real/self._b) if not self._a else
                  other*(1/self));
        return other/other.__class__(self);
    return other/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  if sys.version_info[0] < 3 :

    def __floordiv__(self,other) :
      """Return the floor of the real part of self/other"""
      return self.__class__((self/other)._a.__floor__());

    def __rfloordiv__(self,other) :
      """Return the floor of the real part of other/self"""
      return self.__class__((other/self)._a.__floor__());

    def __mod__(self,other) :
      """Return the remainder from floordiv"""
      return self - self//other*other;

    def __rmod__(self,other) :
      """Return the remainder from rfloordiv"""
      return other - other//self*self;

    def __divmod__(self,other) :
      """Return quotient and remainder"""
      q = self//other;
      return (q, self-q*other);

    def __rdivmod__(self,other) :
      """Return quotient and remainder"""
      q = other//self;
      return (q, other-q*self);

  def __pow__(self,other) :
    """Return a number raised to a power; integer powers give exact answer"""
    if not other.imag :
      other = other.real;
    if isinstance(other,float) :
      if isnan(other) : return nan;
      if isinf(other) :
        b = abs(self);
        return _1 if b == 1 else _0 if (b<1)==(other>0) else inf;
      other = rational(other);
    if isinstance(other,rational) and other._b == 1 :
      other = other._a;
    if not self :
      if other.imag or other < 0:
        raise ZeroDivisionError('0 to negative or complex power');
      else :
        return _0 if other else _1;
    if isint(other) :
      if other < 0 :
        return (1/self)**-other;
      x = self.__class__(_1);
      s = self;
      while other :
        if other&1 : x*=s;
        other >>= 1;
        if not other : break;
        s *= s;
      return x;
    try :
      return (self.__class__(other)*self.log()).exp();
    except :
      return exp(other*self.log());

  def __rpow__(self,other) :
    try :
      return self.__class__(other)**self;
    except :
      if isinstance(other,(float,complex)) :
        if not self._b : return other**self._a;    # real power
        if not (isinf(other.real) or isinf(other.imag)) : return nan;
        return _0 if self._a < 0 else nan;
      return other**other.__class__(self);

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return self.__class__(self._a<<other,self._b<<other) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return self.__class__(self._a>>other,self._b>>other) if other >= 0 else self<<-other;

  def bstr(self,n=5,base=10) :
    """Return a string representation of self, using rational.bstr"""
    if not self._b :
      return self._a.bstr(n,base);
    if not self._a :
      return self._b.bstr(n,base) + '*i';
    return self._a.bstr(n,base) + '+' + self._b.bstr(n,base) + '*i';

  def arg(self,ratio=False) :
    """Return the argument of self; if ratio, as a fraction of 2pi"""
    if not self : raise ZeroDivisionError('zero does not have an argument')
    a = r = None;
    if not self._b :
      r = rational(1-sgn(self._a),4);
    elif not self._a :
      r = rational(sgn(self._b),4);
    elif abs(self._a) == abs(self._b) :
      r = rational(sgn(self._b)*(2-sgn(self._a)),8);
    else :
      a = _atan2(self._b,self._a);
    if ratio :
      return a/tau if r==None else r;
    else :
      return tau*r if a==None else a;

  def log(self,base=None) :
    """Return the log of the number as an xrational"""
    base = rational(base) if base != None else e;
    if base.imag or base <= 0 or base == 1 : raise ValueError('bad base');
    if not self : return inf if base < 1 else -inf;
    d = _ln(base);
    return self.__class__(_ln(abs(self))/d,self.arg()/d);
    
  def exp(self) :
    """Return exp(self) as an xrational"""
    i = self._b;
    m = _exp(self._a);
    return self.__class__(m*_xcos(i),m*_xsin(i));
    
  def approximate(self,accuracy=None) :
    return self.__class__(self._a.approximate(accuracy),self._b.approximate(accuracy));

_0=rational(0);
_1=rational(1);
_i=xrational(_0,_1);
_half = rational(1,2);
_hi = xrational(_0,_half);

# 327 bits :
e = 1+1/rational(tuple(chain.from_iterable((2*i,1,1) for i in xrange(30))));
# 321 bits :
log2e = rational((1,2,3,1,6,3,1,1,2,1,1,1,1,3,10,1,1,1,2,1,1,1,1,3,2,3,1,13,7,4,1,1,1,7,2,4,1,1,2,5,14,1,10,1,4,2,18,3,1,4,1,6,2,7,3,3,1,13,3,1,4,4,1,3,1,1,1,1,2,17,3,1,2,32,1,1,1,1,3,1,4,5,1,1,4,1,3,9,8,1,1,7,1,1,1,1,1,1,1,4,5,4,32,1,19,2,1,1));
# 315 bits :
pi = rational((3,7,15,1,292,1,1,1,2,1,3,1,14,2,1,1,2,2,2,2,1,84,2,1,1,15,3,13,1,4,2,6,6,99,1,2,2,6,3,5,1,1,6,8,1,7,1,2,3,7,1,2,1,1,12,1,1,1,3,1,1,8,1,1,2,1,6,1,1,5,2,2,3,1,2,4,4,16,1,161,45,1,22,1,2,2,1,4,1,2));
tau = 2*pi;
hpi = pi/2;
qpi = pi/4;
# 263 bits :
root2 = rational(tuple(min(i,2) for i in xrange(1,105))); # root2**2 > 2 [see froot2]
roothalf = 1/root2;
# 261 bits :
froot2 = root2 - 1;    # required for _atan: froot2 > (1-froot2)/(1+froot2)
if froot2 < (1-froot2)/(1+froot2) : raise ValueError('root2 too small for atan');

_SIGNIFICANCE = 80;   # bits of significance for below functions
MIN_SIGNIFICANCE = 16;    # somewhat arbitrary
MAX_SIGNIFICANCE = 256;   # based on transcendental constants

def set_significance(significance=None) :
  """Set/return number of bits of significance for transcendental functions"""
  global _SIGNIFICANCE
  if not isint(significance) :
    if significance != None :
      raise TypeError('significance must be an integer');
  elif not MIN_SIGNIFICANCE <= significance <= MAX_SIGNIFICANCE :
    raise ValueError('significance must be between %d and %d',
                     MIN_SIGNIFICANCE, MAX_SIGNIFICANCE);
  else :
    _SIGNIFICANCE = significance;
  return _SIGNIFICANCE;

def _checkaccuracy(a,za,zb,ra,rb) :    # assume za,zb,ra,rb all positive
  d = za*rb;
  return abs(a*(d-zb*ra)) <= d;    # abs(z-r)/z*a <= 1

def _exp(x) :
  n = x.__round__();
  x -= n;
  if x <= 0 :
    if x :
      return e**n/_expp(-x);
    return e**n;
  return e**n*_expp(x);

def _expp(x) :   # 0 < x <= 1/2
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  t = 0;    # compute expm1 to full significance, then add 1 at the end
  s = 1;
  for i in count(1) :
    s *= x/i;
    t += s;
    if s<<_SIGNIFICANCE <= t : break;
  return 1+t.approximate(1<<(_SIGNIFICANCE+8));

def _xsin(t) :
  """Return sin(t) as a rational"""
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (_0,roothalf,_1,roothalf,_0,-roothalf,-_1,-roothalf)[int(r)];
  return _sin(t);

def _xcos(t) :
  """Return cos(t) as a rational"""
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (_1,roothalf,_0,-roothalf,-_1,-roothalf,_0,roothalf)[int(r)];
  return _sin((t-hpi)%tau-pi);

def _atan2(y,x) :
  if not x :
    return hpi*sgn(y);
  a = _atan(y/x);
  return a if x > 0 else a+(sgn(y) or 1)*pi;

def _atan(z) :
  if z < 0 :
    return -_atan(-z);
  if z > 1 :
    return hpi - _atan(1/z);
  if z > froot2 :
    return qpi - _atan((1-z)/(1+z)) if z != -1 else qpi;
  # 0 <= z <= v2-1
  z = z.approximate(1<<(_SIGNIFICANCE+16));
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w;
    t += s/i;
    if abs(s)<<_SIGNIFICANCE <= z : break;
  return t.approximate(1<<(_SIGNIFICANCE+8));

def _ln(z) :
  if z <= 1 :
    if z <= 0 :
      raise ValueError('math domain error');
    if z < 1 :
      return -_ln(1/z);
    return _0;
  if z == e : return _1
  b = bit_length(int(z)) - 1;
  z >>= b;    # 1 <= z < 2
  if z > root2 :
    z >>= 1;
    b += 1;
  # v2/2 < z <= v2
  return (-_mln1p(1-z) if z < 1 else _mln1p(1-1/z) if z > 1 else 0)+b/log2e;

def _mln1p(x) :    # z = 1-x; -ln z, for v2/2 < z < 1
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  t = s = x;    # 0 < x < 1-v2/2
  for i in count(2) :
    s *= x;
    t += s/i;
    if s<<_SIGNIFICANCE <= x : break;
  return t.approximate(1<<(_SIGNIFICANCE+8));

def _sin(z) :
  z = (z+pi)%tau - pi;
  if abs(z) > hpi :
    z = sgn(z)*pi - z;
  # -hpi <= z <= hpi
  z /= 27;
  z = z.approximate(1<<(_SIGNIFICANCE+16));
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w/(i*(i-1));
    t += s;
    if abs(s)<<(_SIGNIFICANCE+5) <= abs(z) : break;
  for i in xrange(3) :
    t = 3*t - 4*t**3;
  return t.approximate(1<<(_SIGNIFICANCE+8));

# math functions

def exp(x) :
  if isinstance(x,(float,complex)) :
    if isnan(x.real) : return nan;
    if isinf(x.real) :
      if x.real < 0 : return 0;
      if isnan(x.imag) or isinf(x.imag) : return nan;
      r = x.imag/float(hpi)%4;
      s = int(r);
      if r == s :
        return inf if isinstance(x,float) else \
          complex(*((inf,nan),(nan,inf),(-inf,nan),(nan,-inf))[s]);
      else :
        return complex(*((inf,inf),(-inf,inf),(-inf,-inf),(inf,-inf))[s]);
    if isnan(x.imag) or isinf(x.imag) : return nan;
  return xrational(x).exp() if x.imag else _exp(rational(x));

def expm1(x) :
  return exp(x)-1;

def log(x,base=e) :
  if isinstance(x,(float,complex)) :
    if base.imag or base <= 0 or base == 1 : raise ValueError('bad base');
    b = log(base);
    if isnan(x.real) :
      return complex(inf/b,sgn(x.imag)*hpi/b) if isinf(x.imag) else nan;
    if isinf(x.real) :
      if isinf(x.imag) :
        return complex(inf/b,qpi/b*(1+(1-sgn(x.real)))*sgn(x.imag));
      return inf/b if x.real > 0 else complex(inf/b,pi/b);
    if isinf(x.imag) :
      return complex(inf/b,sgn(x.imag)*hpi/b);
    if isnan(x.imag) : return nan;
  return xrational(x).log(base) if x.imag else rational(x).log(base);

def log1p(x) :
  return log(_1+x);

def log10(x) :
  return log(x,10);

def log2(x) :
  return log(x,2);

def sin(x) :
  if isinstance(x,(float,complex)) and (
    isinf(x.real) or isinf(x.imag) or isnan(x.real) or isnan(x.imag)) :
    return nan;
  if x.imag :
    ix = _i*x;
    return ((-ix).exp()-ix.exp())*_hi;
  return _xsin(x.real);

def cos(x) :
  if isinstance(x,(float,complex)) and (
    isinf(x.real) or isinf(x.imag) or isnan(x.real) or isnan(x.imag)) :
    return nan;
  if x.imag :
    ix = _i*x;
    return ((-ix).exp()+ix.exp())*_half;
  return _xcos(x.real);

def tan(x) :
  if isinstance(x,(float,complex)) and (
    isinf(x.real) or isinf(x.imag) or isnan(x.real) or isnan(x.imag)) :
    return nan;
  return sin(x)/cos(x);

def atan2(y,x) :
  if y.imag or x.imag :
    raise ValueError('math domain error');
  x,y = x.real, y.real;
  if isinstance(x,float) and isinf(x) or isinstance(y,float) and isinf(y) :
    return atan(y/x);
  return xrational(x,y).arg();

def atan(x) :
  if isinstance(x,(float,complex)) :
    if isnan(x.real) or isnan(x.imag) :
      return nan;
    if isinf(x.imag) :
      return nan;    #?
    if isinf(x.real) :
      return nan if x.imag else hpi if x.real > 0 else -hpi;
  if not x.real and abs(x.imag)==1 :
    return complex(0,sgn(x.imag)*inf);
  return ((1-_i*x)/(1+_i*x)).log()*_hi;

def acos(x) :
  return atan2((_1-x*x)**.5,x);

def asin(x) :
  return atan2(x,(_1-x*x)**.5);

def cosh(x) :
  if isinstance(x,(float,complex)) :
    if isnan(x.real) or isnan(x.imag) or isinf(x.imag) :
      return nan;
    if isinf(x.real) :
      return complex(x.real*cos(x.imag),x.real*sin(x.imag)) if x.imag else inf;
  return (exp(x)+exp(-x))/2;

def sinh(x) :
  if isinstance(x,(float,complex)) :
    if isnan(x.real) or isnan(x.imag) or isinf(x.imag):
      return nan;
    if isinf(x.real) :
      return complex(x.real*cos(x.imag),x.real*sin(sgn(x.real)*x.imag)) if x.imag else x.real;
  return (exp(x)-exp(-x))/2;

def tanh(x) :
  if isinstance(x,(float,complex)) :
    if isnan(x.real) or isnan(x.imag) :
      return nan;
    if isinf(x.real) :
      return _1*sgn(x);
  c = cosh(x);
  if not c :
    return sgn(sinh(x).imag)*inf;
  return sinh(x)/c;

def atanh(x) :
  if not x.imag and abs(x.real) == 1 :
    return sgn(x.real)*inf;
  if isinstance(x,complex) :
    if x.imag :
      if not x.real :
        return i*tan(x.imag);
      if isinf(x.real) :
        return nan;    #?
    else :
      x = x.real;
  if isinstance(x,float) :
    if isnan(x) :
      return nan;
    if isinf(x) :
      return xrational(0,hpi*sgn(x));
  x = rational(x);
  return ((1+x)/(1-x)).log()/2;

def acosh(x) :
  return atanh((_1-_1/(x*x))**.5);

def asinh(x) :
  return sgn(x) * atanh((_1+_1/(x*x))**-.5) if x else 0;

# random math functions

def degrees(x) :
  return x/qpi*45;

def radians(x) :
  return x*qpi/45;

def ldexp(x,i) :
  return rational(x)<<i;

def modf(x) :
  i,f = rational(abs(x)).__divmod__(1);
  s = sgn(x);
  return rational(s*f,s*i)

def pow(x,y) :
  return rational(x)**y;

def sqrt(x) :
  return rational(x)**.5;

def trunc(x) :
  return x.__trunc__();

def fsum(iterable) :
  s = _0;
  for i in iterable : s+=i;
  return i;

def frexp(x) :
  if not x : return (_0,0);
  x = rational(x);
  e = int(log2(abs(x))//1) + 1;
  return (x>>e,e);

def fmod(x,y) :
  return rational(x)%y;

def floor(x) :
  return rational(x)//1;

def ceil(x) :
  return -floor(-x);

def factorial(x) :
  x = rational(x);
  if x.imag or x < 0 or x._b != 1 : raise ValueError('arg must be nonnegative integer');
  y = 1;
  for n in range(2,x._a+1) :
    y *= n;
  return y;

def hypot(x,y) :
  try :
    return (rational(x)**2 + rational(y)**2)**_half;
  except :    # x and/or y is a nan or inf
    return abs(x)+abs(y);

def copysign(x,y) :
  if not x :
    return mathcopysign(x,y);
  if not y and isinstance(y,float) :
    y = mathcopysign(1,y);
  else :
    y = -1 if y < 0 else 1;
  try :
    return rational(abs(x))*y;
  except :    # x is a nan or inf
    return mathcopysign(x,y);

def fabs(x) :
  try :
    return rational(abs(x));
  except :    # x is a nan or inf
    return abs(x);

#def erf(x)
#def erfc(x)
#def gamma(x)
#def lgamma(x)
