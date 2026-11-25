# YiIntr：内置证据、起点及有限构造的核对

新 Reg／Carry⁺ 均是新类型上的对应谓词，不能送回旧接口。
全树定理验证证据确由形状携带；这不是新 Legal 的闭包或序数值验收。
最后的否定只针对本篇 Ready 的无条件化，不否定乙线或其它内置方案。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrCheck where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Data.Sum.Base using (inj₁; inj₂)
open import OCF.Align.YiIntrCore
open import OCF.Align.YiIntrFinite

data Edge : LF → LF → Set where
  e-suc : ∀ {x} → Edge x (suc x)
  e-lim : ∀ {f} n → Edge (f n) (lim f)
  e-first : ∀ {k c w b t p g} → Edge t (lc k c w b t p g)
  e-branch : ∀ {k c w b t p g} η e → Edge (g η e) (lc k c w b t p g)

data Below : LF → LF → Set where
  one : ∀ {a b} → Edge a b → Below a b
  more : ∀ {a b c} → Below a b → Edge b c → Below a c

reach-edge : ∀ {a b c} → Reach a b → Edge b c → Below a c
reach-edge here e = one e
reach-edge (via-suc p) e = more (reach-edge p e-suc) e
reach-edge (via-lim n p) e = more (reach-edge p (e-lim n)) e
reach-edge (via-first p) e = more (reach-edge p e-first) e
reach-edge (via-branch η q p) e = more (reach-edge p (e-branch η q)) e

root-bound : ∀ {k c w b t p g} →
  Below (suc k) (lc k c w b t p g)
root-bound {p = p} = reach-edge p e-first

Reg : LF → Set
Reg zero = ⊤
Reg (suc x) = Reg x
Reg (lim f) = ∀ n → Reg (f n)
Reg (lc k c w b t p g) =
  Below (suc k) (lc k c w b t p g) × Reg k × Reg t ×
  (∀ η e → Reg (g η e))

all-Reg : ∀ x → Reg x
all-Reg zero = tt
all-Reg (suc x) = all-Reg x
all-Reg (lim f) = λ n → all-Reg (f n)
all-Reg (lc k c w b t p g) =
  root-bound , all-Reg k , all-Reg t , (λ η e → all-Reg (g η e))

Carry⁺ : LF → Set
Carry⁺ zero = ⊤
Carry⁺ (suc x) = Carry⁺ x
Carry⁺ (lim f) = ∀ n → Carry⁺ (f n)
Carry⁺ (lc k c w b t p g) =
  Reg (lc k c w b t p g) × Lgl k c × Nested k c ×
  Carry⁺ t × (∀ η e → Carry⁺ (g η e))

all-Carry⁺ : ∀ x → Carry⁺ x
all-Carry⁺ zero = tt
all-Carry⁺ (suc x) = all-Carry⁺ x
all-Carry⁺ (lim f) = λ n → all-Carry⁺ (f n)
all-Carry⁺ (lc k c w b t p g) =
  all-Reg (lc k c w b t p g) , w , b , all-Carry⁺ t ,
  (λ η e → all-Carry⁺ (g η e))

-- 不接受外部 Carry／Legal 参数，守卫完全取结点自己的字段。
start-node : LF → LF
start-node zero = zero
start-node (suc x) = suc x
start-node (lim f) = lim f
start-node (lc k c w b t p g) = g c (inj₁ refl , w , b)

start-lc : ∀ k c w b t p g →
  start-node (lc k c w b t p g) ≡ g c (inj₁ refl , w , b)
start-lc k c w b t p g = refl

tw₂-start : start-node tw₂ ≡ tw₁
tw₂-start = refl

tw₃-start : start-node tw₃ ≡ tw₂
tw₃-start = refl

tw₃-carry⁺ : Carry⁺ tw₃
tw₃-carry⁺ = all-Carry⁺ tw₃

-- 只读同一棵树，外部证书的一致性为定义性相等。
module TreeOnly (P : LF → Set) (run : LF → Raw zero) where
  eval : Σ LF P → Raw zero
  eval (x , p) = run x

  certificate-coherence : ∀ x (p q : P x) → eval (x , p) ≡ eval (x , q)
  certificate-coherence x p q = refl

  lim-function-coherence : ∀ (f : ℕ → LF) (p q : ∀ n → P (f n)) →
    (λ n → eval (f n , p n)) ≡ (λ n → eval (f n , q n))
  lim-function-coherence f p q = refl

  seed-call : LF → Raw zero
  seed-call x = run (start-node x)

-- Ready 的前提不能删去：输入仍是本骨架的闭树，自动带 Carry⁺。
flat : LF
flat = lim (λ _ → zero)

zero-world-shape : (w : World zero) → CanonicalWorld w → omega w ≡ suc zero
zero-world-shape .world0 cw-zero = refl

-- 用沿路径遗传的谓词，避免对两个极限函数的索引相等作匹配。
NoFlat : LF → Set
NoFlat zero = ⊤
NoFlat (suc x) = NoFlat x
NoFlat (lim f) = (∀ n → NoFlat (f n)) × (f zero ≡ zero → ⊥)
NoFlat (lc k c w b t p g) = ⊥

reach-NoFlat : ∀ {a b} → Reach a b → NoFlat b → NoFlat a
reach-NoFlat here r = r
reach-NoFlat (via-suc p) r = reach-NoFlat p r
reach-NoFlat (via-lim n p) (r , nz) = reach-NoFlat p (r n)
reach-NoFlat (via-first p) ()
reach-NoFlat (via-branch η e p) ()

one-not-zero : _≡_ {A = LF} (suc zero) zero → ⊥
one-not-zero ()

no-ready-flat-successor : Ready (suc flat) → ⊥
no-ready-flat-successor (r-suc w (cw-lim ws p cs) strong) = proj₂ bad refl
  where
  nf : NoFlat (lim (λ n → omega (ws n)))
  nf = (λ n → subst NoFlat (sym (zero-world-shape (ws n) (cs n))) tt) ,
    (λ q → one-not-zero (trans (sym (zero-world-shape (ws zero) (cs zero))) q))
  bad : NoFlat flat
  bad = reach-NoFlat p nf

no-total-ready : (∀ x → Ready x) → ⊥
no-total-ready total = no-ready-flat-successor (total (suc flat))

flat-successor-carry⁺ : Carry⁺ (suc flat)
flat-successor-carry⁺ = all-Carry⁺ (suc flat)

-- 检查内部证据是否已成为分支树可观察的数据。
path-mark : ∀ {a b} → Reach a b → ℕ
path-mark here = zero
path-mark (via-suc p) = zero
path-mark (via-lim n p) = n
path-mark (via-first p) = zero
path-mark (via-branch η e p) = zero

node-mark : LF → ℕ
node-mark zero = zero
node-mark (suc x) = zero
node-mark (lim f) = zero
node-mark (lc k c w b t p g) = path-mark p

coord-base : Raw zero
coord-base = G.lim (λ _ → raw1)

coord : Raw zero
coord = G.suc coord-base

coord-lawful : Lgl zero coord
coord-lawful = (λ _ → inj₁ refl) , (λ _ → tt)

coord-guard : ℕ → Gd zero raw1 coord
coord-guard n = inj₂ (inj₂ (n , inj₁ refl)) , coord-lawful , raw0-Nested coord

actual : ℕ → LF
actual n = Ω̂ (CountResult.ready
  (positiveWorld coord coord-lawful (proj₁ (coord-guard n))))

actual-mark : ∀ n → node-mark (actual n) ≡ n
actual-mark n = refl

zero-not-oneᴺ : _≡_ {A = ℕ} zero (suc zero) → ⊥
zero-not-oneᴺ ()

actual-differ : actual zero ≡ actual (suc zero) → ⊥
actual-differ p = zero-not-oneᴺ (cong node-mark p)

RootIrr : LF → Set
RootIrr zero = ⊤
RootIrr (suc x) = ⊤
RootIrr (lim f) = ⊤
RootIrr (lc k c w b t p g) = ∀ η e e′ → g η e ≡ g η e′

tw₃-not-root-irr : RootIrr tw₃ → ⊥
tw₃-not-root-irr irr = actual-differ
  (irr coord (coord-guard zero) (coord-guard (suc zero)))
```

`no-total-ready` 精确否定本次第一支充分条件与规范 World／Ready 配方的
无条件全域化。闭输入 suc(flat) 本身存在且自动带 Carry⁺，
不是假定一个矛盾的折叠接口再推出空结论。
这说明“证据内置后 Ω 自动封闭”不能从本次骨架推出；
它不排除在已生成域中继续生产 Ready，也不排除放宽第一支条件的其它方案。

TreeOnly 只消去同一 LF 上的外部证书；结点内部的 w、b、p、g 已是树的一部分。
换掉内部证据得到另一棵树时，本篇没有证明两者相等或 run 输出相等。
seed-call 只调用一次起点分支，不是 ψ，没有 next／grow／output-step。

`tw₃-not-root-irr` 给这里不能略过的一项具体失败：坐标
`suc (lim (const raw1))` 有两份真实的 Gd 证据，其 Cp 分别选择第 0、1
项；坐标自身的 Lgl 与 Nested 相同。两次构造的输出 lc 内，位置字段
p 的首个 via-lim 分别保存 0、1。actual-mark 为 refl，actual-differ
通过观察该字段否定两棵 LF 相等。因此本篇 tw₃ 不满足原 Legal 的
irr 字段在新类型上的同形陈述，不能宣称已有新 Legal-tw₃。
否定只涉及本篇选择的环境生成与内置字段，不否定所有内置方案或正确 ψ。
