# Shamir

Shamir secret sharing as implemented by `fastcrypto_tbls::polynomial::Poly` over scalars.

| File | Contents |
|---|---|
| `Steps.lean` | The functions of `polynomial.rs` as black boxes (`Api`) and what we expect from them (`Contracts`). |
| `Recovery.lean` | `recover_c0` on `t` shares of a dealt polynomial returns the dealt secret, whichever `t` shares are used. |
| `Privacy.lean` | Fewer than `t` shares reveal nothing about the secret. |
| `Dkg.lean` | Summing dealings, the core of `complete_dkg`: the summed shares recover the sum of the secrets. |
