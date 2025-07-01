""" bitstring classes """

__all__ = ['bitstrings']

# big-endian version implemented with list of ints

from conversions import isint, lmap, xrange, bit_length
from numfuns import xm2gcd

inf = float('inf');

_CB = 128;    # half of threshold chunk size for sequential chunking

def _chunkify(x,l,B) :
  """return a list of B-sized chunks for int x of length l"""
  n = (l+B-1)//B;    # number of B-chunks
  y = [0]*n;
  y[-1] = b = x << ((B-l)%B);
  l = bit_length(b);    # everything else is 0
  if l <= B : return y;
  O = max(1,_CB//B);    # number of B-chunks per last stage (final offset)
  S = O*B;    # target size of chunks at end of halvings
  N = (l+B-1)//B;   # number of relevant B-chunks [i.e., eliding leading zeroes]
  if N :
    z = n-1-N;    # last irrelevant B-chunk
    k = bit_length((N+O-1)//O-1);    # max number of halvings required
    for k in xrange(k-1,-1,-1) :
      o = O<<k;    # offset between created chunks
      s = S<<k;    # size of chunks being created
      m = (1<<s)-1;    # mask
      for i in xrange(n-1,z+o,-o<<1) :
        y[i-o] = y[i] >> s;
        y[i] &= m;
  if O > 1 :
    m = (1<<B)-1;
    for i in xrange(n-1,-1,-O) :
      x = y[i];
      while x :
        y[i] = x&m;
        x >>= B;
        i -= 1;
  return y;

def _filll(self,x) :
  """or value x into list self._x"""
  B = self._B;
  l = self._l;
  v = self._x;
  x <<= (B-l)%B;
  xl = bit_length(x);
  if xl <= B :
    v[-1] |= x;
  else :
    for i,x in enumerate(reversed(_chunkify(x,xl+(-xl%B),B)),1) :
      v[-i] |= x;

def _fillr(self,b,other) :
  """fill list self._x starting at bit b, with other"""
  x = self._x;
  y = other._x;
  B = self._B;
  C = other._B;
  m = (1<<B)-1;
  if B == C :
    r = b%B;
    b //= B;
    if r :
      c = B-r;
      z = (self._l-1)//B;    # last chunk
      for i,y in enumerate(y,b) :
        x[i] |= y>>r;
        if i < z : x[i+1] = (y<<c)&m;
    else :
      x[b:] = y;
  elif not (B%C or b%C) :   # B is multiple of C (combine Cs to get a B)
    D = B-C;
    q = B//C;    # number of Cs in a B
    for i,y in enumerate(y,b//C) :
      x[i//q] |= y << (D-i%q*C);
  elif not (C%B or b%B) :   # C is a multiple of B (split Cs into Bs)
    q = C//B;    # number of Bs from one C
    m = (1<<B)-1;
    for i,y in enumerate(y) :
      e = b//B+i*q-1;
      for r in xrange(e+q,e,-1) :
        try :
          x[r] = y&m;
        except IndexError :    # last y may be partial
          pass;
        y >>= B;
  else :
    D = B-C;
    try :
      for i,y in enumerate(y) :    # C-bit chunks
        sb = b//B;
        eb = (b+C-1)//B;
        if sb==eb :
          x[sb] |= y<<(D-b%B);
        else :
          sr = b%B;
          x[sb] |= y>>(sr-D);
          for a in xrange(sb+1,eb+1) :
            n = (a-sb)*B+D-sr;
            x[a] |= (y<<n if n >= 0 else y>>-n)&m;
        b += C;
    except IndexError:
      pass;
    x[-1] &= -1<<(-self._l%B);


################################################################

# ._l is number of bits (also len())
# [i] is ith bit where [0] is the leftmost bit as a length-1 bitstring
# slice indexing is also allowed, again by bit
# a comma-separated sequence of indices produces a bitstring which is
#  the left-to-right concatenation of the bitstrings for each index
# ._x is internal representation as either an int or a list of ints
# ._B is the maximum number of bits in each of those ints
# only the last (or only) int can hold fewer than _B bits
# if ._x is an int, the lsb is the rightmost bit of the string
# if ._x is a list, the rightmost bit of the bitstring is
#   (._x[-1]>>(._B-1-._l%._B))&1

def __init__(self,a=None,b=None) :
  """Create a bitstring from int a and length abs(b), or
     from string, bytes instance, or bitstring a.
     For int a, if b is negative, the bits of a are reversed.
     For strings, bytes, and bitstrings, if b, a is reversed."""
  if a is None :
    self._x = self._l = 0;
    return;
  B = self._B;
  if isinstance(a,type(self)) :
    self._l = l = a._l;
    self._x = a._x[:] if l > B else a._x;
    if b : self *= -1;
    return;
  if isinstance(a, str) :
    if B == 8 :
      self._l = l = len(a)<<3;
      self._x = lmap(ord,reversed(a) if b else a);
      if l <= B : self._x = l and self._x[0];
      return;
    else :
      a = _bitstring[8](a,b);
      b = None;
  elif isinstance(a, bytes) :
    if B == 8 :
      self._l = l = len(a)<<3;
      self._x = [x for x in (reversed(a) if b else a)];
      if l <= B : self._x = l and self._x[0];
      return;
    else :
      a = _bitstring[8](a,b);
      b = None;
  if isinstance(type(a),bitstrings) :
    self._l = l = a._l;
    if l <= B :
      self._x = __int__(a);
      if b : self *= -1;
      return;
    if l <= a._B :
      self._x = _chunkify(a._x,l,B);
      if b : self *= -1;
      return;
    self._x = [0]*((l+B-1)//B);
    _fillr(self,0,a);
    if b : self *= -1;
    return;
  if not isint(a) :
    raise TypeError('value must be integer');
  if not isint(b) :
    raise TypeError('length must be integer');
  l = abs(b);
  a &= (1<<l)-1;
  self._l = l;    # number of bits
  if l <= B :
    self._x = a;
  else :
    self._x = _chunkify(a,l,B);
  if b < 0 : self *= -1;

def __copy__(self) :
  """Return a copy of self"""
  return type(self)(self);

def __int__(self) :
  """Return the int that is the big-endian interpretation of the bitstring"""
  B = self._B;
  l = self._l;
  if l <= B :
    return self._x;
  z = (B-l)%B;    # number of zeroes at end
  x = self._x;
  n = len(x);    # at least 2
  o = _CB//B;
  if o > 1 :
    y = [];
    for k in xrange(n%o,n+o-1,o) :
      n = 0;
      for i in xrange(max(0,k-o),k) :
        n = (n<<B) | x[i];
      y.append(n);
    n = len(y);
    x = y;
    B = o*B;
  while n > 1 :
    if n&1 :
      y = x[:1];
      r = xrange(1,n,2);
    else :
      y = [];
      r = xrange(0,n,2);
    for i in r :
      y.append((x[i]<<B)|x[i+1]);
    B <<= 1;
    n = len(y);
    x = y;
  return y[0]>>z;

def __repr__(self) :
  """Return a string representing the bitstring"""
  return '%s(0x%%0%dx,%d)'%(type(self).__name__,(self._l+3)//4,self._l)%(int(self));

def __str__(self) :
  """Return a string representing the bitstring"""
  return '%%0%dx'%((self._l+3)//4)%(int(self));

def __len__(self) :
  """Return the length of the bitstring"""
  return self._l;

def __bool__(self) :
  """Return True unless the bitstring has length 0"""
  return not not self._l;

__nonzero__ = __bool__

def __eq__(self,other) :
  """Return True iff self and other are the same bitstring"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l == other._l and (
    self._x == other._x if self._B == other._B else __int__(self) == __int__(other));

def __ne__(self,other) :
  """Return True iff self and other are not the same bitstring"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l != other._l or (
    self._x != other._x if self._B == other._B else __int__(self) != __int__(other));

def __lt__(self,other) :
  """Return True iff self is a proper initial substring of other"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l < other._l and self == other[0:self._l];

def __le__(self,other) :
  """Return True iff self is an initial substring of other"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l <= other._l and self == other[0:self._l];

def __ge__(self,other) :
  """Return True iff other is an initial substring of self"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l >= other._l and self[:other._l] == other;

def __gt__(self,other) :
  """Return True iff other is a proper initial substring of self"""
  if not isinstance(type(other),bitstrings) :
    return NotImplemented;
  return self._l > other._l and self[:other._l] == other;

def __invert__(self) :
  """Return the bitwise complement of self"""
  B = self._B;
  l = self._l;
  if l <= B :
    return type(self)(((1<<l)-1)-self._x,l);
  b = type(self)(0,l);
  v = b._x;
  l %= B;
  m = (1<<B)-1;
  for i,x in enumerate(self._x) :
    v[i] = m-x;
  if l : v[-1] ^= (1<<(B-l))-1;
  return b;

def __neg__(self) :
  """Return the two's complement of self"""
  return type(self)(-__int__(self),self._l);

def __pos__(self) :
  """Return self"""
  return self;

def __ilshift__(self,n) :    # actually, rotate
  """Rotate left self by n bits"""
  if not isint(n) :
    return NotImplemented;
  B = self._B;
  l = self._l;
  n %= l;
  if not n : return self;
  if l <= B :
    self._x = ((self._x<<n)|(self._x>>(l-n)))&((1<<l)-1);
  else :
    x = __int__(self);
    self._x = _chunkify(((x<<n)|(x>>(l-n)))&((1<<l)-1),l,B);
  return self;

def __lshift__(self,n) :
  """Return result of rotating self n bits left"""
  return __ilshift__(type(self)(self),n);

def __irshift__(self,n) :    # actually, rotate
  """Rotate right self by n bits"""
  if not isint(n) :
    return NotImplemented;
  B = self._B;
  l = self._l;
  n %= l;
  if not n : return self;
  if l <= B :
    self._x = ((self._x>>n)|(self._x<<(l-n)))&((1<<l)-1);
  else :
    x = __int__(self);
    self._x = _chunkify(((x>>n)|(x<<(l-n)))&((1<<l)-1),l,B);
  return self;

def __rshift__(self,n) :
  """Return result of rotating self n bits right"""
  return __irshift__(type(self)(self),n);

def __ixor__(self,other) :
  """Bitwise xor other to self"""
  B = self._B;
  l = self._l;
  x = self._x;
  if isinstance(type(other),bitstrings) :
    if l != other._l :
      raise TypeError('bitstrings must have same length');
    if l <= B :
      self._x ^= __int__(other);
      return self;
    if other._B == B :
      for i,o in enumerate(other._x) :
        x[i] ^= o;
      return self;
    other = __int__(other);
  if isint(other) and -1 <= other>>l <= 0 :
    other &= (1<<l)-1;
    if l <= B :
      self._x ^= other;
    else :
      l %= B;
      if l : other <<= (B-l);
      i = -1;
      m = (1<<B)-1;
      while other :
        x[i] ^= other&m;
        other >>= B;
        i -= 1;
    return self;
  return NotImplemented;

def __xor__(self,other) :
  """Return bitwise xor of self and other"""
  return __ixor__(type(self)(self),other);

__rxor__ = __xor__

def __iand__(self,other) :
  """Bitwise and other to self"""
  B = self._B;
  l = self._l;
  x = self._x;
  if isinstance(type(other),bitstrings) :
    if l != other._l :
      raise TypeError('bitstrings must have same length');
    if l <= B :
      self._x &= __int__(other);
      return self;
    if other._B == B :
      for i,o in enumerate(other._x) :
        x[i] &= o;
      return self;
    other = __int__(other);
  if isint(other) and -1 <= other>>l <= 0 :
    other &= (1<<l)-1;
    if l <= B :
      self._x &= other;
    else :
      l %= B;
      if l : other <<= (B-l);
      i = len(x)-1;
      while i >= 0 :
        x[i] &= other;
        other >>= B;
        i -= 1;
    return self;
  return NotImplemented;

def __and__(self,other) :
  """Return bitwise and of self and other"""
  return __iand__(type(self)(self),other);

__rand__ = __and__

def __ior__(self,other) :
  """Bitwise or other to self"""
  B = self._B;
  l = self._l;
  x = self._x;
  if isinstance(type(other),bitstrings) :
    if l != other._l :
      raise TypeError('bitstrings must have same length');
    if l <= B :
      self._x |= __int__(other);
      return self;
    if other._B == B :
      for i,o in enumerate(other._x) :
        x[i] |= o;
      return self;
    other = __int__(other);
  if isint(other) and -1 <= other>>l <= 0 :
    other &= (1<<l)-1;
    if l <= B :
      self._x |= other;
    else :
      l %= B;
      if l : other <<= (B-l);
      i = -1;
      m = (1<<B)-1;
      while other :
        x[i] |= other&m;
        other >>= B;
        i -= 1;
    return self;
  return NotImplemented;

def __or__(self,other) :
  """Return bitwise or of self and other"""
  return __ior__(type(self)(self),other);

__ror__ = __or__

def __iadd__(self,other) :
  """Add other to self, discard carry"""
  B = self._B;
  l = self._l;
  if isinstance(type(other),bitstrings) :
    if l != other._l :
      raise TypeError('bitstrings must have same length');
    other = int(other);
  elif isint(other) :
    if not (-1 <= other>>l <= 0) :
      raise ValueError('int has too many bits');
  else :
    return NotImplemented;
  if l <= B :
    self._x = (self._x+other)&((1<<l)-1);
  else :
    self._x = _chunkify((int(self)+other)&((1<<l)-1),l,B);
  return self;

def __add__(self,other) :
  """Return sum of self and other, discarding carry"""
  return __iadd__(type(self)(self),other);

__radd__ = __add__

def __isub__(self,other) :
  """Subtract other from self, discarding carry"""
  B = self._B;
  l = self._l;
  if isinstance(type(other),bitstrings) :
    if l != other._l :
      raise TypeError('bitstrings must have same length');
    other = int(other);
  elif isint(other) :
    if not (-1 <= other>>l <= 0) :
      raise ValueError('int has too many bits');
  else :
    return NotImplemented;
  if l <= B :
    self._x = (self._x-other)&((1<<l)-1);
  else :
    self._x = _chunkify((int(self)-other)&((1<<l)-1),l,B);
  return self;

def __sub__(self,other) :
  """Return self minus other, discarding carry"""
  return __isub__(type(self)(self),other);

def __rsub__(self,other) :
  """Return other minus self, discarding carry"""
  l = self._l;
  if isint(other) :
    if -1 <= other>>l <= 0 :
      return type(self)((other-int(self))&((1<<l)-1), l);
    else :
      return ValueError('int has too many bits');
  return NotImplemented;


def __getitem__(self,key) :
  """Return bitstring gotten by concatenating the indexed portion(s) of self,
but if key is an int, return the indexed bit as an int"""
  bit = isint(key);
  if not isinstance(key,tuple) :
    key = (key,);
  B = self._B;
  l = self._l;
  z = l%B;
  x = 0;
  n = 0;
  for k in key :
    if isint(k) :
      if -l <= k < l :
        k %= l;
        if l <= B :
          x = (x<<1) | ((self._x>>(l-1-k))&1);
        else :
          y = self._x[k//B];
          x = (x<<1) | ((y>>(B-1-k%B))&1);
        n += 1;
      else :
        raise IndexError('bitstring index out of range');
    elif isinstance(k,slice) :
      s = k.indices(l);
      if s[2] == 1 :    # optimization for step==1
        ls = s[1]-s[0];
        if ls :
          x <<= ls;
          n += ls;
          m = (1<<ls)-1;
          if l <= B :
            x |= (self._x>>(l-s[1]))&m;
          else :
            sb = s[0]//B;
            eb = (s[1]-1)//B
            if sb == eb :   # starts and ends in same block
              x |= (self._x[sb]>>(-s[1]%B))&m;
            else :    # start and end in different blocks
              y = self._x[sb] & ((1<<(B-s[0]%B))-1);
              for i in xrange(sb+1,eb) :
                y = (y<<B)|self._x[i];
              b = -s[1]%B;    # bits discarded from last B-chunk
              x |= (y<<(B-b))|(self._x[eb]>>b);
      else :
        for k in xrange(*s) :
          if l <= B :
            x = (x<<1) | ((self._x>>(l-1-k))&1);
          else :
            x = (x<<1) | ((self._x[k//B]>>(B-1-k%B))&1);
          n += 1;
    else :
      raise TypeError('bitstring index not int or slice');
  return x if bit else type(self)(x,n);

def __setitem__(self,key,value) :    # this makes bitstring mutable!
  """Set the specified portion(s) of key from successive bits of value"""
  B = self._B;
  l = self._l;
  if not isinstance(key,tuple) :
    key = (key,);
  n = 0;
  for k in key :
    if isint(k) :
      if -l <= k < l :
        n += 1;
      else :
        raise IndexError('bitstring index out of range');
    elif isinstance(k,slice) :
      start,stop,step = k.indices(l);
      n += max(0,(stop-start+step-(1 if step>0 else -1)))//step;
    else :
      raise TypeError('bitstring index not int or slice');
  if isinstance(type(value),bitstrings) :
    if value._l != n :
      raise TypeError('value wrong size');
    value = __int__(value);
  elif isint(value) :
    if value >= 1<<n :
      raise TypeError('value too big');
  else :
    raise TypeError('value not bitstring or int');
  for k in key :
    if isint(k) :
      n -= 1;
      k %= l;
      if l <= B :
        if value&(1<<n) :
          self._x |= 1<<(l-1-k);
        else :
          self._x &= ~(1<<(l-1-k));
      else :
        if value&(1<<n) :
          self._x[k//B] |= 1<<(B-1-k%B);
        else :
          self._x[k//B] &= ~(1<<(B-1-k%B));
    elif isinstance(k,slice) :
      s = k.indices(l);
      if s[2] == 1 and B > 1 and s[1]-s[0] > 1:    # optimize for step==1
        ls = s[1]-s[0];
        m = (1<<ls)-1;
        v = (value>>(n-ls))&m;
        if l <= B :
          self._x = self._x&~(m<<(l-s[1])) | (v<<(l-s[1]));
        else :
          sb = s[0]//B;
          eb = (s[1]-1)//B;
          b = -s[1]%B;    # unaffected bits to right
          if sb == eb :
            self._x[sb] = self._x[sb]&~(m<<b) | (v<<b);
          else :
            c = B-s[0]%B;    # affected bits in first chunk
            self._x[sb] = self._x[sb]&(-1<<c)|(v>>(ls-c));
            m = (1<<B)-1;
            for i in xrange(sb+1,eb) :
              self._x[i] = (v>>(B*(eb-i)-b))&m;
            self._x[eb] = self._x[eb]&((1<<b)-1)|((v<<b)&m);
        n -= ls;
      else :
        for k in xrange(*s) :
          n -= 1;
          if l <= B :
            if value&(1<<n) :
              self._x |= 1<<(l-1-k);
            else :
              self._x &= ~(1<<(l-1-k));
          else :
            if value&(1<<n) :
              self._x[k//B] |= 1<<(B-1-k%B);
            else :
              self._x[k//B] &= ~(1<<(B-1-k%B));

def _iconcat(self,*others) :
  """Common section of __concat__ and __iconcat__"""
  B = self._B;
  if B<inf:  m = (1<<B)-1;
  x = self._x;
  l = self._l;
  for other in others :
    if isint(other) and 0 <= other <= 1 :
      if l <= B :
        if l < B :
          self._x = x = (x<<1)|other;
        else :
          self._x = x = [x,other<<(B-1)]
      else :
        lr = l%B
        if lr :
          if other : x[-1] |= 1<<(B-1-lr);
        else :
          x.append(other<<(B-1));
      self._l = l = l+1;
      continue;
    elif isinstance(type(other),bitstrings) :
      oB = other._B;
      ol = other._l;
      nl = l+ol;
      if l <= B :
        if nl <= B :
          self._x = x = (x<<ol)+__int__(other);
          self._l = l = nl;
          continue;
        elif ol <= oB :
          y = (x<<ol)|other._x;
          self._l = l = nl;
          self._x = _chunkify(y,l,B);
          continue;
        else :
          self._x = [x<<(B-l)]+[0]*((nl-1)//B);
          self._l = nl;
          _fillr(self,l,other);
          l = nl;
          continue;
      self._x += [0]*((nl-1)//B-(l-1)//B);
      self._l = nl;
      if ol <= oB :
        _filll(self,other._x);
      else :
        _fillr(self,l,other);
      l = nl;
    else :        
      raise TypeError('can only concatenate bits and bitstrings');
  return self;

def __iconcat__(self,*others) :
  """concat bits or bitstrings to self"""
  if self in others :    # avoid mutating args before using them
    c = type(self)(self);    # copy
    others = tuple(c if o is self else o for o in others);
  return _iconcat(self,*others);

def __concat__(self,*others) :
  """Return a new bitstring formed by concatenating the args, each a bit or a bitstring"""
  return _iconcat(type(self)(self),*others);

def __itacnoc__(self,*others) :
  """Concatenate others to self on the left"""
  x = __int__(self);
  l = self._l;
  for other in others :
    if isint(other) and 0 <= other <= 1 :
      x |= other<<l;
      l += 1;
    elif isinstance(type(other),bitstrings) :
      x |= __int__(other)<<l;
      l += other._l;
    else :
      raise TypeError('not bitstring');
  B = self._B;
  self._l = l;
  if l <= B :
    self._x = x;
  else :
    self._x = _chunkify(x,l,B);
  return self;
  
def __tacnoc__(self,*others) :    # concatenate backwards
  """Return a new bitstring formed by concatening the args in reverse order"""
  x = __int__(self);
  l = self._l;
  for other in others :
    if isint(other) and 0 <= other <= 1 :
      x |= other<<l;
      l += 1;
    elif isinstance(type(other),bitstrings) :
      x |= __int__(other)<<l;
      l += other._l;
    else :
      raise TypeError('not bitstring');
  return type(self)(x,l);

def __itrunc__(self,l) :
  """Truncate self to length |l|; if l < 0 truncate from left"""
  if not isint(l) :
    raise IndexError('length not an integer');
  B = self._B;
  if l < 0 :
    l = -l;
    if l >= self._l :    # extend with zeroes
      if l > B :    # nothing to do unless need to make list
        if self._l <= B :
          x = self._x;
          self._x = [0]*((l+B-1)//B);
          self._x[-1] = x << (B-l)%B;
        else :
          ox = self._x;
          ol = len(ox);    # old list's length
          self._x = x = [0]*((l+B-1)//B-ol) + ox;
          o = (self._l-l)%B;    # bit offset
          if o :    # need to shift
            m = (1<<B)-1;
            if (B-self._l)%B < (B-l)%B :   # must shift left
              for i in xrange(-min(ol+1,len(x)),-1) :
                x[i] = (x[i]<<o)&m | (x[i+1]>>(B-o));
              x[-1] = (x[-1]<<o)&m;
            else :                 # must shift right
              for i in xrange(-1,-ol) :
                x[i] = (x[i] >> (B-o)) | (x[i-1] << o)&m
              x[-ol] >>= B-o;
    elif l <= B :
      if self._l <= B :
        self._x &= (1<<l)-1;
      else :
        self._x = (((self._x[-2]<<B)|self._x[-1]) >> ((B-self._l)%B))&((1<<l)-1);
    else :
      x = self._x;
      o = (self._l-l)%B;
      nl = (l+B-1)//B;    # new length
      if o :    # need to shift
        m = (1<<B)-1;
        if (B-self._l)%B < (B-l)%B :   # must shift left
          for i in xrange(-nl,-1) :
            x[i] = (x[i]<<o)&m | (x[i+1]>>(B-o));
          x[-1] = (x[-1]<<o)&m;
        else :
          for i in xrange(-1,-nl-1,-1) :
            x[i] = (x[i] >> (B-o)) | (x[i-1] << o)&m
      del x[:len(x)-nl];    # truncate
  elif l >= self._l :    # extend with zeroes
    if l <= B :
      self._x <<= l-self._l;
    else :
      if self._l <= B :
        self._x = [self._x<<(B-self._l)] if self._l else [];
      self._x += [0]*((l+B-1)//B-len(self._x));
  else :    # truncate
    x = self._x;
    if l <= B :
      self._x = x[0]>>(B-l) if self._l > B else x>>(self._l-l);
    else :
      del x[(l+B-1)//B:];
      if l%B : x[-1] &= -1<<(B-l%B);
  self._l = l;
  return self;

def __trunc__(self,l) :
  """Return a bitstring formed by truncating self to length |l|; if l < 0, from left"""
  if not isint(l) :
    raise IndexError('length not an integer');
  if l < 0 :
    B = self._B;
    if self._l <= max(B,-l) :
      return __itrunc__(type(self)(self),l);
    s = type(self)();
    if -l <= B :
      s._x = (((self._x[-2]<<B)|self._x[-1]) >> ((B-self._l)%B))&((1<<-l)-1);
    else :
      o = (self._l+l)%B
      nl = o-l;    # new length in best case
      s._x = x = self._x[-((nl+B-1)//B):];
      if o :    # have to shift
        m = (1<<B)-1;
        for i in xrange(len(x)-1) :
          x[i] = (x[i]<<o)&m | (x[i+1]>>(B-o));
        if (B-1-l)//B < len(x) :
          del x[-1];
        else :
          x[-1] = (x[-1]<<o)&m;
    s._l = -l;
    return s;
  if l >= self._l :    # extend with zeroes
    return __itrunc__(type(self)(self),l);
  B = self._B;
  x = self._x;
  r = type(self)();
  if l <= B:
    r._x = x[0]>>(B-l) if self._l > B else x>>(self._l-l);
  else :
    r._x = x[:(l+B-1)//B];
    if l%B : r._x[-1] &= -1<<(B-l%B);
  r._l = l;
  return r;

def __imul__(self,n) :
  """If n is an int,
  concatenate the bitstring to itself |n| times, bitreversed if n < 0.
  If n is a bitstring with length len(self),
  treat both bitstrings as GF(2) polynomials and multiply mod x^l-1."""
  if isint(n) :
    if n <= 0 :
      if n :
        n = -n;
        l = self._l;
        for i in xrange(l//2) :
          self[i],self[l-1-i] = self[l-1-i],self[i];
      else :
        self._x = 0;
        self._l = 0;
    if n > 1 :
      y = type(self)(self);
      for _ in xrange(n-1) :
        self.iconcat(y);
    return self;
  elif isinstance(type(n),bitstrings) :
    if self._l != n._l :
      raise TypeError('bitstrings must have same length');
    m = type(self)(self);
    if n is self :
      n = type(self)(n);
    self &= 0;
    for i in range(self._l) :
      if n[i] : self ^= m;
      m >>= 1;
    return self;
  return NotImplemented;

def __mul__(self,n) :
  """If n is an integer,
  return a bitstring comprising |n| copies of self, bitreversed if n < 0.
  If n is a bitstring of length l = len(self),
  return product of the two bitstrings, treated as GF(2) polynomials mod x^l-1.
"""
  return __imul__(type(self)(self),n);

def __itruediv__(self,other) :
  if isinstance(type(other),bitstrings) :
    if self._l != other._l :
      raise TypeError('bitstrings must have same length');
    return __imul__(self,__pow__(other,-1));
  return NotImplemented

def __truediv__(self,other) :
  return __itruediv__(type(self)(self),other);

def __rtruediv__(self,n) :
  if n==1 :
    return __pow__(self,-1);
  else :
    return NotImplemented;
    
def __ipow__(self,e) :
  """Return nonnegative integer power n of self using bitstring multiplication"""
  if isint(e) :
    l = self._l;
    B = self._B;
    if e <= 1 :
      if e <= 0 :
        if e :
          g,u,v = xm2gcd((1<<l)+1,int(self)) ; # + not | to handle l == 0
          if g != 1 :
            raise ZeroDivisionError('base has no inverse');
          if l > 2 :
            v = (v>>2) | ((v&3)<<(l-2));    # convert lsb 0 -> msb 0
        else :
          v = (1<<l)>>1;    # in case l==0
        if l <= B :
          self._x = v;
        else :
          self._x = _chunkify(v,l,B);
        e = -e;
      if e <= 1 :
        return self;
    b = type(self)(self);
    n = 1 << (bit_length(e)-2);
    while n :
      self *= self;
      if e&n :
        self *= b;
      n >>= 1;
    return self;
  else :
    return NotImplemented;

def __pow__(self,e) :
  """Return nonnegative integer power e of self using bitstring multiplication"""
  return __ipow__(type(self)(self),e);

def __split__(self,C) :
  """Return a list of type(self) elements whose concatenation == self.
     Each list element has nonzero length <= abs(C). C must be nonzero.
     If C > 0, all but the last list element has length == C.
     If C < 0, all but the first list element has length == C."""
  l = self._l;
  t = type(self);
  B = t._B;  
  if C < 0 :
    C = -C;
    if l > C :
      o = -l%C;
      if o :
        x = bitstrings(C)(0,o).iconcat(self)._x;
        # for i,b in enumerate(x) :
        #  x[i] = t(b,C);
        # x[0].itrunc(o-C);
        if C <= B :
          for i,b in enumerate(x) :
            x[i] = z = t();
            z._x = b;
            z._l = C;
          x[0]._l = C-o;
        else :
          for i,b in enumerate(x) :
            x[i] = z = t();
            z._x = _chunkify(b,C,B);
            z._l = C;
          x[0].itrunc(o-C);
        return x;
  if l <= C  : return [t(self)] if l else [];
  x = bitstrings(C)(self)._x;
  l %= C;
  # for i,b in enumerate(x) :
  #  x[i] = t(b,C);
  # if l : z.itrunc(l);
  if C <= B :
    for i,b in enumerate(x) :
      x[i] = z = t();
      z._x = b;
      z._l = C;
    if l :
      z._x >>= C-l;
      z._l = l;
  else :
    for i,b in enumerate(x) :
      x[i] = z = t();
      z._x = _chunkify(b,C,B);
      z._l = C;
    if l :
      z.itrunc(l);
  return x;

def __bytes__(self,C=-8) :
  """Return a bytes instance with equivalent hex value"""
  return bytes(map(int,self.split(C)));

def __string__(self,C=-8) :
  """Return a string s where self == bitstring(s)"""
  return ''.join(map(chr,map(int,self.split(C))));

################################################################

_bitstring = {};  # chunk -> bitstring

class bitstrings(type) :
  """Class to create bitstring types"""

  def __new__(cls,chunk=inf) :
    try :
      return _bitstring[chunk];
    except :
      pass;
    if not isint(chunk) and chunk != inf :
      raise TypeError('chunk must be infinite or an integer');
    if chunk<=0 :
      raise ValueError('chunk must be positive');
    d = dict(_B=chunk,
             __init__=__init__,
             __repr__=__repr__,
             __str__=__str__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __bool__ = __bool__,
             __nonzero__=__nonzero__,
             __int__=__int__,    # convert to single integer
             __len__=__len__,    # number of bits
             __invert__=__invert__,
             __neg__=__neg__,
             __pos__=__pos__,
             __getitem__=__getitem__,
             __setitem__=__setitem__,
             __imul__=__imul__,  # repeat (int other), or convolve (bitstrings)
             __mul__=__mul__,
             __ipow__=__ipow__,
             __pow__=__pow__,
             __itruediv__=__itruediv__,
             __truediv__=__truediv__,
             __rtruediv__=__rtruediv__,
             __ilshift__=__ilshift__,    # rotate left
             __irshift__=__irshift__,    # roate right
             __lshift__=__lshift__,
             __rshift__=__rshift__,
             __ixor__=__ixor__,
             __xor__=__xor__,
             __rxor__=__xor__,
             __ior__=__ior__,
             __or__=__or__,
             __ror__=__or__,
             __iand__=__iand__,
             __and__=__and__,
             __rand__=__and__,
             __iadd__=__iadd__,
             __add__=__add__,
             __radd__=__add__,
             __isub__=__isub__,
             __sub__=__sub__,
             __rsub__=__rsub__,
             iconcat=__iconcat__,
             concat=__concat__,
             itacnoc=__itacnoc__,
             tacnoc=__tacnoc__,
             itrunc=__itrunc__,
             trunc=__trunc__,
             split=__split__,
             copy=__copy__,
             bytes=__bytes__,
             string=__string__,
           );
    name = 'bitstring%d'%(chunk) if chunk < inf else 'bitstring';
    _bitstring[chunk] = b = type.__new__(cls,name,(),d);
    return b;

  def __init__(self,*args,**kwargs) :
    return;

  def __hash__(self) :
    return hash(self.__name__);

  def __eq__(self,other) :
    return self is other;

  def __ne__(self,other) :
    return not self is other;

     
bitstring = bitstrings();
bitstrings(8);
