library pointycastle.src.bigint_util;

import 'dart:typed_data';

class BigIntUtil {
  const BigIntUtil._();

  static final BigInt three = new BigInt.from(3);
  static final BigInt fullU32 = new BigInt.from(0xffffffff);
  static final BigInt fullU16 = new BigInt.from(0xffff);
  static final BigInt fullU8 = new BigInt.from(0xff);
  static final BigInt fullU4 = new BigInt.from(0xf);

  // Workaround for https://github.com/dart-lang/sdk/issues/32626
  static BigInt modPow(BigInt b, BigInt e, BigInt m) {
    if (e < BigInt.one) {
      return BigInt.one;
    }
    if (b < BigInt.zero || b > m) {
      b = b % m;
    }
    var r = BigInt.one;
    while (e > BigInt.zero) {
      if ((e & BigInt.one) > BigInt.zero) {
        r = (r * b) % m;
      }
      e >>= 1;
      b = (b * b) % m;
    }
    return r;
  }

  static BigInt fromBytes(int sign, List<int> bytes) {
    BigInt v;

    if (sign != 0) {
      v = _fromBytesInternal(bytes, true);
    } else {
      v = _fromBytesInternal(bytes, false);
    }

    if (sign < 0) {
      v = -v;
    }

    return v;
  }

  static BigInt _fromBytesInternal(List<int> bytes, [bool fixSign = false]) {
    if (bytes == null || bytes.length == 0) {
      return BigInt.zero;
    }

    bool neg = false;
    if (!fixSign && bytes[0] & 0xFF > 0x7F) {
      neg = true;
    }

    if (neg) {
      BigInt v = BigInt.zero;
      for (int i = 0; i < bytes.length; i++) {
        v = (v << 8) | ~new BigInt.from(((bytes[i] & 0xFF) - 256));
      }
      return ~v;
    } else {
      BigInt v = BigInt.zero;
      for (int i = 0; i < bytes.length; i++) {
        v = (v << 8) | new BigInt.from(bytes[i] & 0xFF);
      }
      return v;
    }
  }

  static Uint8List toBytes(BigInt bigInt) {
    String str;
    bool neg = false;
    if (bigInt.isNegative) {
      str = (~bigInt).toRadixString(16);
      neg = true;
    } else {
      str = bigInt.toRadixString(16);
    }
    int p = 0;
    int len = str.length;

    int blen = (len + 1) ~/ 2;
    int boff = 0;
    Uint8List bytes;
    if (neg) {
      if (len & 1 == 1) {
        p = -1;
      }
      int byte0 = ~int.parse(str.substring(0, p + 2), radix: 16);
      if (byte0 < -128) byte0 += 256;
      if (byte0 >= 0) {
        boff = 1;
        bytes = new Uint8List(blen + 1);
        bytes[0] = -1;
        bytes[1] = byte0;
      } else {
        bytes = new Uint8List(blen);
        bytes[0] = byte0;
      }
      for (int i = 1; i < blen; ++i) {
        int byte = ~int.parse(str.substring(p + (i << 1), p + (i << 1) + 2),
            radix: 16);
        if (byte < -128) byte += 256;
        bytes[i + boff] = byte;
      }
    } else {
      if (len & 1 == 1) {
        p = -1;
      }
      int byte0 = int.parse(str.substring(0, p + 2), radix: 16);
      if (byte0 > 127) byte0 -= 256;
      if (byte0 < 0) {
        boff = 1;
        bytes = new Uint8List(blen + 1);
        bytes[0] = 0;
        bytes[1] = byte0;
      } else {
        bytes = new Uint8List(blen);
        bytes[0] = byte0;
      }
      for (int i = 1; i < blen; ++i) {
        int byte =
            int.parse(str.substring(p + (i << 1), p + (i << 1) + 2), radix: 16);
        if (byte > 127) byte -= 256;
        bytes[i + boff] = byte;
      }
    }
    return bytes;
  }

  static bool testBit(BigInt bigInt, int n) {
    return (bigInt & (BigInt.one << n)).sign != 0;
  }

  static int lowestSetBit(BigInt x) {
    if (x.sign == 0) return -1;
    int r = 0;
    while ((x & fullU32).sign == 0) {
      x >>= 32;
      r += 32;
    }
    if ((x & fullU16).sign == 0) {
      x >>= 16;
      r += 16;
    }
    if ((x & fullU8).sign == 0) {
      x >>= 8;
      r += 8;
    }
    if ((x & fullU4).sign == 0) {
      x >>= 4;
      r += 4;
    }
    if ((x & three).sign == 0) {
      x >>= 2;
      r += 2;
    }
    if ((x & BigInt.one).sign == 0) ++r;
    return r;
  }

  /** test primality with certainty >= 1-.5^t */
  static bool isProbablePrime(BigInt bigInt, int t) {
    if (bigInt.isEven) return false;
    int i = 0;
    BigInt x = bigInt.abs();
    if (bigInt.isValidInt) {
      final int asInt = bigInt.toInt();
      if (asInt <= _lowprimes[_lowprimes.length - 1]) {
        for (i = 0; i < _lowprimes.length; ++i)
          if (asInt == _lowprimes[i]) return true;
        return false;
      }
    }
    i = 1;
    final lplim = new BigInt.from(_lplim);
    while (i < _lowprimes.length) {
      BigInt m = new BigInt.from(_lowprimes[i]);
      var j = i + 1;
      while (j < _lowprimes.length && m < lplim)
        m *= new BigInt.from(_lowprimes[j++]);
      m = x % m;
      while (i < j)
        if ((m % new BigInt.from(_lowprimes[i++])).sign == 0) return false;
    }
    return millerRabin(x, t);
  }

  /** true if probably prime (HAC 4.24, Miller-Rabin) */
  static bool millerRabin(BigInt x, int t) {
    var n1 = x - BigInt.one;
    var k = lowestSetBit(n1);
    if (k <= 0) return false;
    var r = n1 >> k;
    t = (t + 1) >> 1;
    if (t > _lowprimes.length) t = _lowprimes.length;
    for (var i = 0; i < t; ++i) {
      final BigInt a = new BigInt.from(_lowprimes[i]);
      BigInt y = modPow(a, r, x);
      if (y.compareTo(BigInt.one) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while (j++ < k && y.compareTo(n1) != 0) {
          y = modPow(y, BigInt.two, x);
          if (y.compareTo(BigInt.one) == 0) return false;
        }
        if (y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }

  static const List<int> _lowprimes = const [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59,
    61,
    67,
    71,
    73,
    79,
    83,
    89,
    97,
    101,
    103,
    107,
    109,
    113,
    127,
    131,
    137,
    139,
    149,
    151,
    157,
    163,
    167,
    173,
    179,
    181,
    191,
    193,
    197,
    199,
    211,
    223,
    227,
    229,
    233,
    239,
    241,
    251,
    257,
    263,
    269,
    271,
    277,
    281,
    283,
    293,
    307,
    311,
    313,
    317,
    331,
    337,
    347,
    349,
    353,
    359,
    367,
    373,
    379,
    383,
    389,
    397,
    401,
    409,
    419,
    421,
    431,
    433,
    439,
    443,
    449,
    457,
    461,
    463,
    467,
    479,
    487,
    491,
    499,
    503,
    509
  ];
  static final int _lplim = (1 << 26) ~/ _lowprimes[_lowprimes.length - 1];
}
