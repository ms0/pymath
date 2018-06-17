# class rational, implementing Q, the field of rational numbers

from __future__ import division

import sys

from math import floor, log
from itertools import chain, count

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

else :

  xrange = range;

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except :
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(log(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

inf = float('inf');

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
  l = log(a,2)/n;
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

class rational :
  """Rational number class
Instance variables:
  a or numerator: the numerator, an integer
  b or denominator: the denominator, a positive integer
  Note that gcd(a,b) == 1.
Methods:
  __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__,
  __int__, __float__, __round__, __ceil__, __floor__, __trunc__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, cf"""

  def __init__(self,a,b=1) :
    """Create a rational number equal to a/b; attempting b=0 raises ZeroDivisionError
If a is a float or rational (and b==1), return the simplest possible rational
If a is a nonempty list or tuple of integers (and b==1),
 they are interpreted as the terms of a regular continued fraction"""
    if not isint(a) or not isint(b) :
      if b == 1 :
        if isinstance(a,xrational) :
          if a._b : raise TypeError('arg must not be complex')
          a = a._a;
        if isinstance(a,rational) :
          self._a,self._b=a._a,a._b;
          return;
        if isinstance(a,complex) :
          if a.imag : raise TypeError('arg must not be complex')
          a = a.real;
        if isinstance(a,float) :
          x = a;
          m0,m1,n0,n1 = 0,1,1,0;
          for i in xrange(64) :
            ix = floor(x);
            fx = x - ix;        
            iix = int(ix);
            m0,m1,n0,n1 = n0,n1,m0+iix*n0,m1+iix*n1;
            if fx == 0 or n0/n1 == a : break;
            x = 1/fx;
          self._a,self._b = int(n0),int(n1);
          return;
        if a and isinstance(a,(tuple,list)) :
          m0,m1,n0,n1 = 0,1,1,0;
          for i in a :
            if not isint(i) : raise TypeError('cf must be integral');
            if i <= 0 and n1 : raise TypeError('cf terms beyond first must be positive');
            m0,m1,n0,n1 = n0,n1,m0+i*n0,m1+i*n1;
          self._a,self._b = int(n0),int(n1);
          return;
      raise TypeError('Numerator and Denominator must be integers');
    if b < 0 : a,b = -a,-b;
    if not b : raise ZeroDivisionError;
    g = gcd(a,b);
    self._a = int(a//g);
    self._b = int(b//g);

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self._a,self._b) if self._b != 1 else '%d'%(self._a);

  def __repr__(self) :
    """Return a string showing the rational number as it could be input"""
    return 'rational(%d,%d)'%(self._a,self._b) if self._b != 1 else 'rational(%d)'%(self._a);

  def __hash__(self) :
    """Return a hash for the rational number; if an integer, use that integer's hash"""
    return hash(self._a) if self._b == 1 else hash(self._a/self._b);

  def __getattr__(self,name) :
    if name in ('a','numerator') :
      return self._a;
    if name in ('b','denominator') :
      return self._b;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __lt__(self,other) :
    """Return True iff self < other """
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a < self._b*other;
      elif isinstance(other,float) :
        return self < rational(other);
      else :
        return NotImplemented;
    return self._a*other._b < self._b*other._a;

  def __le__(self,other) :
    """Return True iff self <= other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a <= self._b*other;
      elif isinstance(other,float) :
        return self <= rational(other);
      else :
        return NotImplemented;
    return self._a*other._b <= self._b*other._a;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a == self._b*other;
      elif isinstance(other,float) :
        return self == rational(other);
      else :
        return NotImplemented;
    return self._a*other._b == self._b*other._a;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a != self._b*other;
      elif isinstance(other,float) :
        return self != rational(other);
      else :
        return NotImplemented;
    return self._a*other._b != self._b*other._a;

  def __ge__(self,other) :
    """Return True iff self >= other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a >= self._b*other;
      elif isinstance(other,float) :
        return self >= rational(other);
      else :
        return NotImplemented;
    return self._a*other._b >= self._b*other._a;

  def __gt__(self,other) :
    """Return True iff self > other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a > self._b*other;
      elif isinstance(other,float) :
        return self > rational(other);
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
    return rational(-self._a,self._b) if self._a else self;

  def __abs__(self) :
    """Return |self|"""
    return rational(-self._a,self._b) if self._a < 0 else self;

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,complex) :
        return xrational(self)+xrational(other);
      try :
        return self+rational(other);
      except :
        return other+self;
    return rational(self._a*other._b+other._a*self._b,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,complex) :
        return xrational(self)-xrational(other);
      try :
        return self-rational(other);
      except :
        return -other+self;
    return rational(self._a*other._b-other._a*self._b,self._b*other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    if isinstance(other,complex) :
      return xrational(other)-xrational(self);
    return rational(other)-self;

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return rational(self._a*other,self._b);
      if isinstance(other,complex) :
        return xrational(self)*xrational(other);
      try :
        return self*rational(other);
      except :
        return other*self;
    return rational(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return rational(self._a,other*self._b);
      if isinstance(other,complex) :
        return xrational(self)/xrational(other);
      try :
        return self/rational(other);
      except :
        return other.__rtruediv__(self);
    return rational(self._a*other._b,self._b*other._a);

  def __rtruediv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return rational(other*self._b,self._a);
      if isinstance(other,complex) :
        return xrational(other)/xrational(self);
      return rational(other)/self;
    return rational(self._b*other._a,self._a*other._b);

  __div__ = __truediv__
  __rdiv__ = __rtruediv__

  def __floordiv__(self,other) :
    """Return the floor of the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return rational(self._a//(self._b*other));
      if isinstance(other,complex) :
        return xrational(self)//xrational(other);
      try :
        return self//rational(other);
      except :
        return other.__rfloordiv__(self);
    return rational((self._a*other._b)//(self._b*other._a));

  def __rfloordiv__(self,other) :
    """Return the floor of the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return rational((self._b*other)//self._a);
      if isinstance(other,complex) :
        return xrational(other)//xrational(self);
      return rational(other)//self;
    return rational((self._b*other._a)//(self._a*other._b));

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
        return xrational(self)**other;
      other = other.real;
    if not self._a :
      if other < 0 :
        raise ZeroDivisionError;
      else :
        return self if other else rational(1);
    if isinstance(other,float) :
      other = rational(other);
    if isinstance(other,rational) and other._b == 1 :
      other = other._a;
    if isint(other) :
      if other < 0 :
        return rational(self._b**-other,self._a**-other);
      return rational(self._a**other,self._b**other);
    if not isinstance(other,rational) :
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
      return rational(ra**r*ac,rb**r*bc);    # exact result
    return _exp(rational(a,b).log()*r/d)*ac/bc;

  def __rpow__(self,other) :
    return rational(other)**self;

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return rational(self._a<<other,self._b) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return rational(self._a,self._b<<other) if other >= 0 else self<<-other;

  def __float__(self) :
    """Return a floating point approximation to the number"""
    return self._a/self._b;

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

  def __round__(self,n=0) :
    """Return the round of the number"""
    ten2absn = 10**abs(n);
    return ((int((self/ten2absn - half)*ten2absn) if self._a < 0 else
             int(self/ten2absn + half)*ten2absn) if n < 0 else
            -(int(half - self*ten2absn)/ten2absn) if self._a < 0 else
            int(half + self*ten2absn)/ten2absn);

  def log(self,base=None) :
    """Return the log of the number as a rational if finite, else as +-inf"""
    if base != None and (base <= 0 or base == 1) : raise ValueError('bad base');
    if not self._a : return inf if base < 1 else -inf;
    base = rational(base or e);
    d = _ln(base) if base != e else 1;
    return _ln(self)/d;

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
        #if abs((z-rational(o0,o1))/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,o0,o1) :
          n = (q+1)//2;    # min possible term
          x = q;           # max possible term
          while True :
            i = (n+x)//2;
            p0,p1 = m0+i*n0,m1+i*n1;
            #r = rational(p0,p1);
            #if abs((z-r)/z*accuracy) > 1 :
            if not _checkaccuracy(accuracy,za,zb,p0,p1) :
              n = i+1;
            else :
              x = i;
              if x == n :
                return rational(s*p0,p1);
      else :
        r = q + (q*(q+1)*zb*zb < za*za);
        #if abs((z-r)/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,r,1) :
          return rational(r*s);
      m0,m1,n0,n1 = n0,n1,o0,o1;
      a,b = b, a-q*b;
    return self;

half = rational(1,2);

class xrational :
  """Complex Rational number class
Instance variables:
  real: the real part, a rational
  imag: the imaginary part, a rational
Methods:
  __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __pos__, __neg__, __abs__,
  __float__, __complex__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, arg"""

  def __init__(self,real,imag=0) :
    """Create a complex number equal to real+imag*i; real and imag are converted to rational
If real is complex or xrational (and imag==0), return the corresponding xrational"""
    if imag == 0 :
      if isinstance(real,xrational) :
        real,imag = real._a,real._b;
      elif isinstance(real,complex) :
        real,imag = real.real,real.imag;
    self._a = rational(real);
    self._b = rational(imag);
  
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
    return hash(float(self._a) + 1j*float(self._b));

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
        other = xrational(other);
      except :
        return NotImplemented;
    return self._a == other._a and self._b == other._b;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      try :
        other = xrational(other);
      except :
        return NotImplemented;
    return self._a != other._a or self._b != other._b;

  def __bool__(self) :
    """Return True iff self != 0"""
    return bool(self._a) or bool(self._b);

  __nonzero__ = __bool__

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return xrational(-self._a,-self._b);

  def __invert__(self) :
    """Return complex conjugate of self"""
    return xrational(self._a,-self._b);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self._a**2+self._b**2)**half;

  def __float__(self) :
    """Return a floating point approximation to the number if real"""
    if self.imag : raise TypeError('complex');
    return float(self.real);

  def __complex__(self) :
    """Return a floating point [i.e., complex] approximation to the number"""
    return complex(self.real,self.imag);

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        return self+xrational(other);
      except :
        return other+self;
    return xrational(self._a+other._a,self._b+other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        return self-xrational(other);
      except :
        return -other+self;
    return xrational(self._a-other._a,self._b-other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    return xrational(other)-self;

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        return self*xrational(other);
      except :
        return other*self;
    return xrational(self._a*other._a-self._b*other._b,self._a*other._b+self._b*other._a);

  __rmul__ = __mul__

  def __div__(self,other) :
    """Return the quotient of the two numbers"""
    if not other :
      raise ZeroDivisionError;
    if not isinstance(other,self.__class__) :
      try :
        other = xrational(other);
      except :
        return other.__rdiv__(self);
    d = other._a**2 + other._b**2;
    return xrational((self._a*other._a+self._b*other._b)/d,(self._b*other._a-self._a*other._b)/d);

  def __rdiv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      other = xrational(other);
    return other/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  if sys.version_info[0] < 3 :

    def __floordiv__(self,other) :
      """Return the floor of the real part of self/other"""
      return xrational((self/other)._a.__floor__());

    def __rfloordiv__(self,other) :
      """Return the floor of the real part of other/self"""
      return xrational((other/self)._a.__floor__());

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
    if isinstance(other,(complex,xrational)) and not other.imag :
      other = other.real;
    if isinstance(other,float) :
      other = rational(other);
    if isinstance(other,rational) and other._b == 1 :
      other = other._a;
    if not self :
      if isinstance(other,(complex,xrational)) or other < 0:
        raise ZeroDivisionError('0 to negative or complex power');
      else :
        return rational(0 if other else 1);
    if isint(other) :
      if other < 0 :
        return (1/self)**-other;
      x = xrational(1);
      s = self;
      while other :
        if other&1 : x*=s;
        other >>= 1;
        if not other : break;
        s *= s;
      return x;
    return (xrational(other)*self.log()).exp();


  def __rpow__(self,other) :
    return xrational(other)**self;

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return xrational(self._a<<other,self._b<<other) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return xrational(self._a>>other,self._b>>other) if other >= 0 else self<<-other;

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
      a = xatan2(self._b,self._a);
    if ratio :
      return a/tau if r==None else r;
    else :
      return tau*r if a==None else a;

  def log(self,base=None) :
    """Return the log of the number as an xrational"""
    if base != None and (base <= 0 or base == 1) : raise ValueError('bad base');
    if not self : raise ZeroDivisionError('complex 0 has no log');
    c = rational(base or e);
    d = _ln(c) if c != e else 1;
    return xrational(_ln(abs(self))/d,self.arg()/d);
    
  def exp(self) :
    """Return exp(self) as an xrational"""
    i = self.imag;
    m = _exp(self.real);
    return xrational(m*xcos(i),m*xsin(i));
    
  def approximate(self,accuracy=None) :
    return xrational(self.real.approximate(accuracy),self.imag.approximate(accuracy));

_0=rational(0);
_1=rational(1);
# 327 bits :
e = 1+1/rational(tuple(chain.from_iterable((2*i,1,1) for i in xrange(30))));
# 314 bits :
log2e = rational((1,2,3,1,6,3,1,1,2,1,1,1,1,3,10,1,1,1,2,1,1,1,1,3,2,3,1,13,7,4,1,1,1,7,2,4,1,1,2,5,14,1,10,1,4,2,18,3,1,4,1,6,2,7,3,3,1,13,3,1,4,4,1,3,1,1,1,1,2,17,3,1,2,32,1,1,1,1,3,1,4,5,1,1,4,1,3,9,8,1,1,7,1,1,1,1,1,1,1,4,5,4,32,1,19,2,1,1));
# 261 bits :
pi = rational((3,7,15,1,292,1,1,1,2,1,3,1,14,2,1,1,2,2,2,2,1,84,2,1,1,15,3,13,1,4,2,6,6,99,1,2,2,6,3,5,1,1,6,8,1,7,1,2,3,7,1,2,1,1,12,1,1,1,3,1,1,8,1,1,2,1,6,1,1,5,2,2,3,1,2,4,4,16,1));
tau = 2*pi;
hpi = pi/2;
qpi = pi/4;
# 256 bits :
root2 = rational(tuple(min(i,2) for i in xrange(1,103))); # root2**2 > 2 [see froot2]
roothalf = 1/root2;
# 254 bits :
froot2 = root2 - 1;    # required for xatan: froot2 > (1-froot2)/(1+froot2)
if froot2 < (1-froot2)/(1+froot2) : raise ValueError('root2 too small for atan');

SIGNIFICANCE = 80;   # bits of significance for below functions
ACCURACY = 1<<256;   # for intermediate computations

def _checkaccuracy(a,za,zb,ra,rb) :    # assume za,zb,ra,rb all positive
  d = za*rb;
  return abs(a*(d-zb*ra)) <= d;    # abs(z-r)/z*a <= 1

def _exp(x) :
  n = round(x);
  x -= n;
  if x <= 0 :
    if x :
      return e**n/_expp(-x);
    return e**n;
  return e**n*_expp(x);

def _expp(x) :   # 0 < x <= 1/2
  x = x.approximate(ACCURACY);
  t = 1;
  s = 1;
  for i in count(1) :
    s *= x/i;
    t += s;
    if s<<SIGNIFICANCE <= t-1 : break;
  return t.approximate(ACCURACY);

def xsin(t) :
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (_0,roothalf,_1,roothalf,_0,-roothalf,-_1,-roothalf)[int(r)];
  return _sin(t);

def xcos(t) :
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (_1,roothalf,_0,-roothalf,-_1,-roothalf,_0,roothalf)[int(r)];
  return _sin((t-hpi)%tau-pi);

def xatan2(y,x) :
  if not x :
    return hpi*sgn(y);
  a = xatan(y/x);
  return a if x > 0 else a+(sgn(y) or 1)*pi;

def xatan(z) :
  if z < 0 :
    return -xatan(-z);
  if z > 1 :
    return hpi - xatan(1/z);
  if z > froot2 :
    return qpi - xatan((1-z)/(1+z)) if z != -1 else qpi;
  # 0 <= z <= v2-1
  z = z.approximate(ACCURACY);
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w;
    t += s/i;
    if abs(s)<<SIGNIFICANCE <= z : break;
  return t.approximate(ACCURACY);

def _ln(z) :
  if z <= 1 :
    if z <= 0 :
      raise ValueError('math domain error');
    if z < 1 :
      return -_ln(1/z);
    return rational(0);
  b = bit_length(int(z)) - 1;
  z >>= b;    # 1 <= z < 2
  if z > root2 :
    z >>= 1;
    b += 1;
  # v2/2 < z <= v2
  return (-_mln1p(1-z) if z < 1 else _mln1p(1-1/z) if z > 1 else 0)+b/log2e;

def _mln1p(x) :    # z = 1-x; -ln z, for v2/2 < z < 1
  x = x.approximate(ACCURACY);
  t = s = x;    # 0 < x < 1-v2/2
  for i in count(2) :
    s *= x;
    t += s/i;
    if s<<SIGNIFICANCE <= x : break;
  return t.approximate(ACCURACY);

def _sin(z) :
  z = (z+pi)%tau - pi;
  if abs(z) > hpi :
    z = sgn(z)*pi - z;
  # -hpi <= z <= hpi
  z /= 27;
  z = z.approximate(ACCURACY);
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w/(i*(i-1));
    t += s;
    if abs(s)<<SIGNIFICANCE <= abs(z) : break;
  for i in xrange(3) :
    t = 3*t - 4*t**3;
  return t.approximate(ACCURACY);
