# quaternion class

# Note -1 has uncountably many square roots, we choose i

__all__ = ['quaternion']

import sys

VERSION2 = int(sys.version.split('.')[0]) < 3;
INTTYPE = (int,long,) if VERSION2 else (int,);
REALTYPE = (int,long,float,) if VERSION2 else (int,float,);
COMPLEXTYPE = (int,long,float,complex) if VERSION2 else (int,float,complex,);

import math    # exp, log, cos, sin, acos

class ParameterError(Exception):
  pass

def islistlike(a) :
  return isinstance(a,(list,tuple));

def isreal(a) :
  return isinstance(a,REALTYPE);

def iscomplex(a) :
  return isinstance(a,COMPLEXTYPE);

class quaternion :
  """
  quaternion class
    quaternion(a) is the real number a
    quaternion(a,b) is the complex number a+bi
    quaternion(a,b,c) is the vector ai+bj+ck
    quaternion(a,b,c,d) is the quaternion a+bi+cj+dk
    + - * / ** abs have their normal meaning
      note that multiplication is not commutative
    ~q is the conjugate of q: ~quaternion(a,b,c,d) == quaternion(a,-b,-c,-d)
    q.s, q.r, q.real, q.scalar are each the scalar (real) part of q
    q.v, q.vector are each the vector part of q as a list
    q.i, q.j, q.k are the respective components of the vector part of q
    q.conjugate is ~q
    q.versor is q/abs(q)
    q.exp is exp(q)
    q.log, q.ln are each [natural] log(q)
      note that quaternion(-a).log == quaternion(math.log(a),math.pi) for a>0
  """
  def __init__(self,*args) :
    self.__dict__['_quaternion__v'] = [0,0,0,0];
    if len(args) == 1 :
      if isinstance(args[0],quaternion) :
        self.__v[:] = args[0].__v;
        return;
      if islistlike(args[0]) :
        args = args[0];
    if len(args) == 1 :
      if iscomplex(args[0]) :
        if isreal(args[0]) :
          self.__v[0] = args[0];
        else :
          self.__v[0:2] = args[0].real,args[0].imag;
        return;
    elif len(args) == 0 :
      return;
    elif len(args) == 2 :
      self.__v[0:2] = args[0],args[1];
    elif len(args) == 3 :
      self.__v[1:] = args[0],args[1],args[2];
    elif len(args) == 4 :
      self.__v[:] = args;
    else : raise TypeError('quaternion takes at most 4 reals or 1 complex');
    for x in self.__v :
      if not isreal(x) : raise TypeError('quaternion components must be real');

  def __hash__(self) :
    if not any(self.__v[2:]) :    # real or complex
      return hash(complex(*self.__v[0:2])) if self.__v[1] else hash(self.__v[0]);
    return hash(tuple(self.__v));

  def __repr__(self) :
    return 'quaternion('+repr(self.__v)+')';

  def __str__(self) :
    return '('+format(self.__v[0],'n')+format(self.__v[1],'+n')+'i'+\
        format(self.__v[2],'+n')+'j'+format(self.__v[3],'+n')+'k)';

  def __eq__(self,other) :
    if isinstance(other,quaternion) :
      return self.__v == other.__v;
    elif isreal(other) :
      return self.__v[0] == other and \
          self.__v[1] == 0 and self.__v[2] == 0 and self.__v[3] == 0;
    elif isinstance(other,complex) :
      return self.__v[0] == other.real and self.__v[1] == other.imag and \
          self.__v[2] == 0 and self.__v[3] == 0;
    else :
      return False;

  def __ne__(self,other) :
    return not self == other;

  def __neg__(self) :
    return quaternion(-self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  def __invert__(self) :
    return quaternion(self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  def __abs__(self) :
    return (self.__v[0]*self.__v[0]+self.__v[1]*self.__v[1]+
            self.__v[2]*self.__v[2]+self.__v[3]*self.__v[3])**.5;

  def __add__(self,other) :
    other = quaternion(other);    # always need a copy
    for i in range(4) :
      other.__v[i] += self.__v[i];
    return other;

  __radd__ = __add__;

  __iadd__ = __add__;

  def __sub__(self,other) :
    other = quaternion(-other);    # always need a copy
    for i in range(4) :
      other.__v[i] += self.__v[i];
    return other;

  __isub__ = __sub__;
 
  def __rsub__(self,other) :
    other = quaternion(other);    # always need a copy
    for i in range(4) :
      other.__v[i] -= self.__v[i];
    return other;

  def __mul__(self,b) :
    b = quaternion(b);
    b.__v[:] = self.__v[0]*b.__v[0] \
        -self.__v[1]*b.__v[1]-self.__v[2]*b.__v[2]-self.__v[3]*b.__v[3], \
         self.__v[0]*b.__v[1]+self.__v[1]*b.__v[0]+self.__v[2]*b.__v[3]- \
         self.__v[3]*b.__v[2],                                           \
         self.__v[0]*b.__v[2]+self.__v[2]*b.__v[0]+self.__v[3]*b.__v[1]- \
         self.__v[1]*b.__v[3],                                           \
         self.__v[0]*b.__v[3]+self.__v[3]*b.__v[0]+self.__v[1]*b.__v[2]- \
         self.__v[2]*b.__v[1];
    return b;

  __imul__ = __mul__;

  def __rmul__(self,b) :
    b = quaternion(b);
    b.__v[:] = b.__v[0]*self.__v[0] \
        -b.__v[1]*self.__v[1]-b.__v[2]*self.__v[2]-b.__v[3]*self.__v[3], \
         b.__v[0]*self.__v[1]+b.__v[1]*self.__v[0]+b.__v[2]*self.__v[3]- \
         b.__v[3]*self.__v[2],                                           \
         b.__v[0]*self.__v[2]+b.__v[2]*self.__v[0]+b.__v[3]*self.__v[1]- \
         b.__v[1]*self.__v[3],                                           \
         b.__v[0]*self.__v[3]+b.__v[3]*self.__v[0]+b.__v[1]*self.__v[2]- \
         b.__v[2]*self.__v[1];
    return b;

  # danger: a*b**-1 != b**-1*a ?
  def __truediv__(self,b) :
    return self.__mul__(quaternion(b).__pow__(-1));

  def __rtruediv__(self,b) :
    return quaternion(b).__truediv__(self);

  __itruediv__ = __truediv__

  __div__ = __truediv__
  __rdiv__ = __rtruediv__
  __idiv__ = __itruediv__

  def __pow__(self,other) :
    if not isinstance(other,NUMTYPE) :
      raise TypeError('exponent must be a number');
    r = real(other);
    if not any(self.__v) :      # special case zero
      if r > 0 : return self;
      else : raise ZeroDivisionError('0 cannot be raised to a nonpositive power');
    if r!=other or int(r)!=r :    # non integer power
      # a**x = exp(log(a)*x)
      return (self.log*other).exp;
    r = int(r);    # integer power
    if not any(self.__v[1:]) :
      return quaternion(self.__v[0]**r);        #real
    if r < 0 :
      a = self.__v[0]*self.__v[0] + self.__v[1]*self.__v[1] + \
          self.__v[2]*self.__v[2] + self.__v[3]*self.__v[3] + 0.;
      q = quaternion(self.__v[0]/a, -self.__v[1]/a, -self.__v[2]/a, -self.__v[3]/a);
      r = -r;
    else :
      q = self;
    result = quaternion(1,0,0,0);
    while r :
      if r&1 : result *= q;
      r >>= 1;        
      if not r : break;
      q *= q;
    return result;

  __ipow__ = __pow__

  def __rpow__(self,other) :
    if not isinstance(other,COMPLEXTYPE) :
      raise TypError('base must be a number');
    return quaternion(other).__pow__(self);

  # NOTE: might want to try to do a better pow computation by leaving
  # the divide to last and doing integer computations up to that point

  def __getitem__(self,key) :
    if isinstance(key,(INTTYPE,slice)) :
      return self.__v[key];
    else :
      raise TypeError('index must be nonnegative integer < 4, or slice');

  def __getattr__(self,name) :
    if name == 's' or name == 'r' or name == 'real' or name == 'scalar':
      return self.__v[0];
    if name == 'v' or name == 'vector' :
      return self.__v[1:];
    if name == 'i' :
      return self.__v[1];
    if name == 'j' :
      return self.__v[2];
    if name == 'k' :
      return self.__v[3];
    if name == 'conjugate' :
      return ~self;
    if name == 'versor' :
      a = abs(self);
      return quaternion(self.__v[0]/a,self.__v[1]/a,self.__v[2]/a,self.__v[3]/a);
    if name == 'exp' :
      ea = math.exp(self.__v[0]);
      av = math.sqrt(self.__v[1]*self.__v[1]+
                     self.__v[2]*self.__v[2]+
                     self.__v[3]*self.__v[3]);
      s = ea*math.sin(av)/av if av else 1;
      return quaternion(ea*math.cos(av),s*self.__v[1],s*self.__v[2],s*self.__v[3]);
    if name == 'log' or name == 'ln' :
      a = abs(self);
      av = math.sqrt(self.__v[1]*self.__v[1]+
                     self.__v[2]*self.__v[2]+
                     self.__v[3]*self.__v[3]);
      if not av and self.__v[0] < 0 :
        return quaternion(math.log(a),math.pi,0,0);
      ac = math.acos(self.__v[0]/a)/av if av else 1./a;
      return quaternion(math.log(a),ac*self.__v[1],ac*self.__v[2],ac*self.__v[3]);
    raise AttributeError('quaternion object has no attribute '+name);

def real(a) :
  if isinstance(a,REALTYPE) : return a;
  if isinstance(a,(complex,quaternion)) : return a.real;
  return None;

NUMTYPE = (int,long,float,complex,quaternion,) if VERSION2 else (int,float,complex,quaternion,);
