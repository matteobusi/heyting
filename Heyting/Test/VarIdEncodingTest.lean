import Heyting.Core.VarIdEncoding

open StructIR

example (v : VarId) : VarIdEncoding.decode (VarIdEncoding.encode v) = v := by
  simpa using VarIdEncoding.decode_encode v

example (k : Nat) : VarIdEncoding.encode (VarIdEncoding.decode k) = k := by
  simpa using VarIdEncoding.encode_decode k
