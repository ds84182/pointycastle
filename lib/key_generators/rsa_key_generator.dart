// Copyright (c) 2013-present, the authors of the Pointy Castle project
// This library is dually licensed under LGPL 3 and MPL 2.0.
// See file LICENSE for more information.

library pointycastle.impl.key_generator.rsa_key_generator;

import "package:pointycastle/api.dart";
import "package:pointycastle/asymmetric/api.dart";
import "package:pointycastle/key_generators/api.dart";
import 'package:pointycastle/src/bigint_util.dart';
import "package:pointycastle/src/registry/registry.dart";

class RSAKeyGenerator implements KeyGenerator {

  static final FactoryConfig FACTORY_CONFIG =
      new StaticFactoryConfig(KeyGenerator, "RSA");

  SecureRandom _random;
  RSAKeyGeneratorParameters _params;

  String get algorithmName => "RSA";

  @override
  void init(CipherParameters params) {
    if (params is ParametersWithRandom) {
      _random = params.random;
      _params = params.parameters;
    } else {
      _random = new SecureRandom();
      _params = params;
    }

    if (_params.bitStrength < 12) {
      throw new ArgumentError("key bit strength cannot be smaller than 12");
    }

    if (!BigIntUtil.testBit(_params.publicExponent, 0)) {
      throw new ArgumentError("Public exponent cannot be even");
    }
  }

  AsymmetricKeyPair generateKeyPair() {
    BigInt p, q, n, e;

    // p and q values should have a length of half the strength in bits
    var strength = _params.bitStrength;
    var pbitlength = (strength + 1) ~/ 2;
    var qbitlength = strength - pbitlength;
    var mindiffbits = strength ~/ 3;

    e = _params.publicExponent;

    // TODO Consider generating safe primes for p, q (see DHParametersHelper.generateSafePrimes)
    // (then p-1 and q-1 will not consist of only small factors - see "Pollard's algorithm")

    // generate p, prime and (p-1) relatively prime to e
    for ( ; ; ) {
      p = generateProbablePrime(pbitlength, 1, _random);

      if (p % e == BigInt.one) {
        continue;
      }

      if (!BigIntUtil.isProbablePrime(p, _params.certainty)) {
        continue;
      }

      if (e.gcd(p - BigInt.one) == BigInt.one) {
        break;
      }
    }

    // generate a modulus of the required length
    for ( ; ; ) {

      // generate q, prime and (q-1) relatively prime to e, and not equal to p
      for ( ; ; ) {
        q = generateProbablePrime(pbitlength, 1, _random);

        if ((q - p).abs().bitLength < mindiffbits) {
          continue;
        }

        if ((q % e) == BigInt.one) {
          continue;
        }

        if (!BigIntUtil.isProbablePrime(q, _params.certainty)) {
          continue;
        }

        if (e.gcd(q - BigInt.one) == BigInt.one) {
          break;
        }
      }

      // calculate the modulus
      n = p * q;

      if (n.bitLength == _params.bitStrength) {
        break;
      }

      // if we get here our primes aren't big enough, make the largest of the two p and try again
      p = p > q ? p : q;
    }

    // Swap p and q if necessary
    if (p < q) {
      var swap = p;
      p = q;
      q = swap;
    }

    // calculate the private exponent
    var pSub1 = (p - BigInt.one);
    var qSub1 = (q - BigInt.one);
    var phi = (pSub1 * qSub1);
    var d = e.modInverse(phi);

    return new AsymmetricKeyPair(new RSAPublicKey(n, e), new RSAPrivateKey(n, d, p, q));
  }

}

BigInt generateProbablePrime(int bitLength, int certainty, SecureRandom rnd) {
  BigInt candidate;

  if (bitLength < 2) {
    candidate = BigInt.one;
  } else {
    candidate = rnd.nextBigInteger(bitLength);

    // force MSB set
    if (!BigIntUtil.testBit(candidate, bitLength - 1)) {
      candidate = candidate | (BigInt.one << (bitLength - 1));
    }

    // force odd
    if (candidate.isEven) {
      candidate += BigInt.one;
    }

    while (!BigIntUtil.isProbablePrime(candidate, certainty)) {
      candidate += BigInt.two;
      if (candidate.bitLength > bitLength) {
        candidate -= BigInt.one << (bitLength - 1);
      }
    }
  }

  return candidate;
}
