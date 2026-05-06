namespace MPC.Adapters.SHA256

abbrev Word :=
  UInt32

def shift (n : Nat) : Word :=
  UInt32.ofNat n

def rotr (x : Word) (n : Nat) : Word :=
  (x >>> shift n) ||| (x <<< shift (32 - n))

def choose (x y z : Word) : Word :=
  (x &&& y) ^^^ (~~~x &&& z)

def majority (x y z : Word) : Word :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : Word) : Word :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

def bigSigma1 (x : Word) : Word :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

def smallSigma0 (x : Word) : Word :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> shift 3)

def smallSigma1 (x : Word) : Word :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> shift 10)

def initialHash : Array Word :=
  #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ]

def roundConstants : Array Word :=
  #[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]

def lengthByte (bitLength shift : Nat) : UInt8 :=
  UInt8.ofNat ((bitLength / (2 ^ shift)) % 256)

def pad (bytes : ByteArray) : ByteArray := Id.run do
  let bitLength := bytes.size * 8
  let mut padded := bytes.push 0x80
  while padded.size % 64 != 56 do
    padded := padded.push 0
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push (lengthByte bitLength shift)
  pure padded

def readWord (bytes : ByteArray) (offset : Nat) : Word :=
  let b0 := (bytes.get! offset).toUInt32
  let b1 := (bytes.get! (offset + 1)).toUInt32
  let b2 := (bytes.get! (offset + 2)).toUInt32
  let b3 := (bytes.get! (offset + 3)).toUInt32
  (b0 <<< shift 24) ||| (b1 <<< shift 16) ||| (b2 <<< shift 8) ||| b3

def blockSchedule (bytes : ByteArray) (offset : Nat) : Array Word := Id.run do
  let mut words := Array.mkEmpty 64
  for i in List.range 16 do
    words := words.push (readWord bytes (offset + i * 4))
  for j in List.range 48 do
    let i := j + 16
    let word :=
      smallSigma1 words[i - 2]! + words[i - 7]! +
        smallSigma0 words[i - 15]! + words[i - 16]!
    words := words.push word
  pure words

def processBlock (bytes : ByteArray) (offset : Nat) (hash : Array Word) : Array Word := Id.run do
  let schedule := blockSchedule bytes offset
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!
  for i in List.range 64 do
    let t1 := h + bigSigma1 e + choose e f g + roundConstants[i]! + schedule[i]!
    let t2 := bigSigma0 a + majority a b c
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  pure #[
    hash[0]! + a, hash[1]! + b, hash[2]! + c, hash[3]! + d,
    hash[4]! + e, hash[5]! + f, hash[6]! + g, hash[7]! + h
  ]

def digestWords (bytes : ByteArray) : Array Word := Id.run do
  let padded := pad bytes
  let mut hash := initialHash
  let mut offset := 0
  while offset < padded.size do
    hash := processBlock padded offset hash
    offset := offset + 64
  pure hash

def hexDigit (n : Nat) : Char :=
  let n := n % 16
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

def pushWordHex (out : String) (word : Word) : String := Id.run do
  let mut out := out
  for shift in [28, 24, 20, 16, 12, 8, 4, 0] do
    out := out.push (hexDigit ((word.toNat / (2 ^ shift)) % 16))
  pure out

def hashBytes (bytes : ByteArray) : String :=
  (digestWords bytes).foldl pushWordHex ""

def hashString (text : String) : String :=
  hashBytes text.toUTF8

end MPC.Adapters.SHA256
