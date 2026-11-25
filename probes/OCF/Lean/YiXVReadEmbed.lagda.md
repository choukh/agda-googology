# YiXVReadEmbed
> 验收文件。档位：编译定理。原嵌入整对的复合、实际下降路径与 Up 经嵌入后的计算等式。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadEmbed where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Unit using (tt)
import Data.Product
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRoute as Route
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadEmbedInput as E

compose : ∀ {cur mid orig v w} (rv : R.Route cur mid v) (rw : R.Route mid orig w) z →
  E.emb rv (E.emb rw z) ≡ E.emb (Route.compose rv rw) z
compose R.here rw z = refl
compose (R.ins {r = r} rv) rw z = cong (E.raise (J.ℓ (S.suc r)) tt) (compose rv rw z)
compose (R.inl {f = f} {d = d} n rv) rw z = cong (E.raise (J.ℓ (S.lim f d)) n) (compose rv rw z)
compose (R.inlu {f = f} {d = d} rv) rw z = cong (E.raise (J.ℓ (S.lim f d)) 0) (compose (rv 0) rw z)

follow : ∀ {top cur orig v} → Down.Down top cur → R.Route cur orig v → Down.Down top orig
follow d R.here = d
follow d (R.ins rv) = follow (Down.down-suc d) rv
follow d (R.inl n rv) = follow (Down.down-lim d n) rv
follow d (R.inlu rv) = follow (Down.down-lim d 0) (rv 0)

model₀ : E.emb R.model₀ (E.emb R.model₀ E.one) ≡ E.one
model₀ = compose R.model₀ R.model₀ E.one
model₁ : Down.src (follow Down.here R.model₁) ≡ Down.src (Down.down-suc Down.here)
model₁ = refl
model-ω : Down.src (follow Down.here R.model-ω) ≡ Down.src (Down.down-lim Down.here 0)
model-ω = refl

up : ∀ {top cur orig v} (d : Down.Down top cur) (rv : R.Route cur orig v)
  x (nx : J.ℓ top S.⊢ S.zero ◃ x) z →
  O.Up (J.ℓ cur) (Down.src d) x nx (Data.Product.proj₁ (E.emb rv z)) ≡
  O.Up (J.ℓ orig) (Down.src (follow d rv)) x nx (Data.Product.proj₁ z)
up d R.here x nx z = refl
up d (R.ins rv) x nx z = up (Down.down-suc d) rv x nx z
up d (R.inl n rv) x nx z = up (Down.down-lim d n) rv x nx z
up d (R.inlu rv) x nx z = up (Down.down-lim d 0) (rv 0) x nx z
```
