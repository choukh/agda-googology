# 有限参照桥：展开后递归子目标的定位
验收文件；编译定理：参照的整行展开、目标基本列前两项及对应参照的结构等价。
本文件没有 R.Rel 到 M 1 的桥；没有证明两种递归动机不能通过其他引理实现。
来源：Level.ψ 的定义与 ψ-≅；EboLeanDef 的基本列规则。入口 YiFBFinite。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFBShape where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiPVF2 as F2
import OCF.Lean.YiFBFinite as Q
open import OCF.BTBO using (module Ord-Ord)

-- 实际 n=4 的参照不展开折叠输出；只展开参照自身的一层。
inner : L.Ordᶜ (L.natᴵ 3) → L.Ordᶜ (L.natᴵ 3)
inner x = L.ψ L.zero (λ q → q) (L.up L.zero x)
chain : ℕ → L.Ordᶜ (L.natᴵ 3)
chain = Ord-Ord.iter inner (L.Ω (L.natᴵ 3))
row : ℕ → L.Ordᶜ (L.suc L.zero)
row n = L.ψ F2.four-p (λ q → L.suc q) (L.up L.zero (chain n))
reference-form : Q.Reference ≡ L.lim row
reference-form = refl
term : E.T
term = AF.ψᴺ 1 (AF.Ωᴺ 4)
cof-term : E.cof term ≡ E.cω
cof-term = refl
term-row-zero : E.fsn term 0 ≡ AF.ψᴺ 1 (AF.Ωᴺ 3)
term-row-zero = refl
term-row-one : E.fsn term 1 ≡ AF.ψᴺ 1 (AF.ψᴺ 3 (AF.Ωᴺ 3))
term-row-one = refl
ref-three : L.Ordᶜ (L.suc L.zero)
ref-three = L.ψ (L.suc (L.suc L.zero)) (λ q → L.suc q) (L.Ω (L.natᴵ 3))
row-zero : row 0 L.≅ ref-three
row-zero = L.ψ-≅ {p = F2.four-p} {σ = λ q → L.suc (L.suc q)}
  {p′ = L.suc (L.suc L.zero)} {σ′ = λ q → L.suc q}
  (L.s≅ L.z≅) (L.Ω-refl (L.natᴵ 3))

row-one-ref : L.Ordᶜ (L.suc L.zero)
row-one-ref = L.ψ (L.suc (L.suc L.zero)) (λ q → L.suc q)
  (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 3)))
row-one-match : row 1 L.≅ row-one-ref
row-one-match = L.ψ-≅ {p = F2.four-p} {σ = λ q → L.suc (L.suc q)}
  {p′ = L.suc (L.suc L.zero)} {σ′ = λ q → L.suc q}
  (L.s≅ L.z≅)
  (L.ψ-≅ {p = L.zero} {σ = λ q → L.suc q}
    {p′ = L.zero} {σ′ = λ q → L.suc q}
    (L.≅ᴵ-refl (L.natᴵ 3)) (L.Ω-refl (L.natᴵ 3)))
```
