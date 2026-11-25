# 全部带类型的声明（逐字提取）
仅为定位索引；完整源码是陈述与范围的依据。

## probes/OCF/Lean/YiE4Base.lagda.md

来源行 19
```agda
Ctx : Set
```

来源行 21
```agda
level : Ctx → B.L
```

来源行 23
```agda
okay : (d : Ctx) → P.Ok (level d)
```

来源行 25
```agda
table : (d : Ctx) → TB.Rb (level d)
```

来源行 27
```agda
base : (d : Ctx) → F.Base (level d)
```

来源行 31
```agda
  collapse : Ctx → O.Tr⁺ B.zero → O.Tr⁺ B.zero
```

来源行 33
```agda
  collapse-eq : ∀ h o r bs β → collapse (h , o , r , bs) β ≡ TB.ψ h o r bs B.zero (P.z≤ h) β (proj₁ (O.Ωt h))
```

来源行 35
```agda
make : B.Tr (B.tw 2) → Ctx
```

来源行 40
```agda
  raw-wire : ∀ q → collapse (make (FR.Step.chain 2 q)) (GI.betaᴱ 3) ≡ FR.Step.out 2 (FR.Step.chain 2 q)
```

## probes/OCF/Lean/YiE4Cut19.lagda.md

来源行 24
```agda
  outer-g : ∀ n → B.Tr (B.tw n) → B.Tr (B.tw (suc n))
```

来源行 26
```agda
  outer-g-eq : ∀ n c → outer-g n c ≡ FR.Step.g n c
```

来源行 28
```agda
  outer-feed : ∀ n → B.Tr (B.tw n) → B.Tr (B.tw n)
```

来源行 31
```agda
  outer-feed-eq : ∀ n c → outer-feed n c ≡ FR.Step.feed n c
```

来源行 33
```agda
  outer-out : ∀ n → B.Tr (B.tw n) → O.Tr⁺ B.zero
```

来源行 36
```agda
  outer-out-eq : ∀ n c → outer-out n c ≡ FR.Step.out n c
```

来源行 40
```agda
  base₀ : F.Base k
```

来源行 42
```agda
  base₀-eq : base₀ ≡ (λ i u → GI.baseᴱ 3 i (P.inc B.zero u))
```

来源行 44
```agda
  branch : B.Tr (B.tw 1) → B.Tr k
```

来源行 47
```agda
  branch-eq : ∀ d → branch d ≡ proj₁ (TB.ψ k (P.Ok-tw 2) (MT.rbᶻ k) base₀ k P.self
    (GI.baseᴱ 3 k (P.ink P.self)) (outer-g 1 d))
```

来源行 50
```agda
c₁ : B.Tr k
```

来源行 52
```agda
a : B.Tr (B.tw 1) → B.L
```

来源行 55
```agda
o₁ : P.Ok h₁
```

来源行 60
```agda
  c₁-actual : c₁ ≡ FR.Step.chain 2 1
```

来源行 62
```agda
  h₁-actual : h₁ ≡ FR.Step.child 2 c₁
```

来源行 66
```agda
  base₁ : F.Base h₁
```

来源行 68
```agda
  base₁-eq : base₁ ≡ (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
```

来源行 70
```agda
  inner-g : B.Tr (B.tw 1) → B.Tr h₁
```

来源行 72
```agda
  inner-g-eq : ∀ d → inner-g d ≡ proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} d (O.Ωt (a d)))
```

来源行 76
```agda
  inner-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
```

来源行 79
```agda
  inner-feed-eq : ∀ d → inner-feed d ≡ proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
    (base₁ (B.tw 1) (P.ink P.self)) (inner-g d))
```

来源行 82
```agda
  inner-out : B.Tr (B.tw 1) → O.Tr⁺ B.zero
```

来源行 84
```agda
  inner-out-eq : ∀ d → inner-out d ≡ TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (inner-g d)
```

来源行 86
```agda
inner-chain : ℕ → B.Tr (B.tw 1)
```

来源行 88
```agda
inner-zero : inner-chain 0 ≡ B.zero
```

来源行 90
```agda
inner-one : inner-chain 1 ≡ proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
  (base₁ (B.tw 1) (P.ink P.self)) (inner-g B.zero))
```

来源行 94
```agda
iter-two : {A : Set} (f : A → A) (z : A) → O.iter f z 2 ≡ f (f z)
```

来源行 96
```agda
inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
```

## probes/OCF/Lean/YiE4Cut20.lagda.md

来源行 24
```agda
row0 : {X : Set} {z : X} (m : F.Keep B.zero X z) (G : X → O.Tr⁺ B.zero) (s : X → X)
  → F.node⁺ m G s ≡ O.limc⁺ (λ n → G (O.iter s z n))
```

来源行 31
```agda
  first-row : TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (proj₁ (O.Ωt h₁))
    ≡ O.limc⁺ (λ n → inner-out (inner-chain n))
```

## probes/OCF/Lean/YiE4Default.lagda.md

来源行 33
```agda
  pre-eq : ∀ n → D.pre n ≡ GI.pre n
```

来源行 36
```agda
  base-eq : ∀ n → D.baseᴱ n ≡ GI.baseᴱ n
```

来源行 38
```agda
  beta-eq : ∀ n → D.betaᴱ n ≡ GI.betaᴱ n
```

来源行 40
```agda
  g-eq : ∀ n → D.Step.g n ≡ FR.Step.g n
```

来源行 42
```agda
  feed-eq : ∀ n → D.Step.feed n ≡ FR.Step.feed n
```

来源行 44
```agda
  out-eq : ∀ n → D.Step.out n ≡ FR.Step.out n
```

来源行 46
```agda
chain-eq : ∀ n q → D.Step.chain n q ≡ FR.Step.chain n q
```

来源行 50
```agda
  output-old : D.output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
```

来源行 53
```agda
module Use (low : U.Missing) where
```

来源行 55
```agda
  first-at-one : FR.FirstMissing
```

来源行 60
```agda
Bound : E.T → O.Tr⁺ B.zero → Set
```

来源行 61
```agda
Bound t x = (h : SI.E.HC t) → SI.E.tree h ≼ K.readRW (proj₁ x)
```

来源行 62
```agda
move-bound : ∀ {s t u v} → s ≡ t → u ≡ v → Bound s u → Bound t v
```

来源行 64
```agda
OriginalAtOne : Set
```

来源行 66
```agda
from-original : OriginalAtOne → U.Missing
```

来源行 70
```agda
to-original : U.Missing → OriginalAtOne
```

来源行 73
```agda
module FromOriginal (low : OriginalAtOne) where
```

来源行 75
```agda
  first-at-one : FR.FirstMissing
```

## probes/OCF/Lean/YiE4Frame.lagda.md

来源行 24
```agda
module Frame (c : B.Tr (B.tw 2)) (c-eq : c ≡ C.c₁)
  (h : B.L) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
  (env-eq : (h , o , r , bs) ≡ Q.make c)
  (β : O.Tr⁺ B.zero) (β-eq : β ≡ A.β)
  (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , r , bs) β))) where
  context-eq : (h , o , r , bs) ≡ A.ctx
```

来源行 25
```agda
  (h : B.L) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
```

来源行 26
```agda
  (env-eq : (h , o , r , bs) ≡ Q.make c)
```

来源行 27
```agda
  (β : O.Tr⁺ B.zero) (β-eq : β ≡ A.β)
```

来源行 28
```agda
  (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , r , bs) β))) where
```

来源行 29
```agda
  context-eq : (h , o , r , bs) ≡ A.ctx
```

来源行 31
```agda
  sealed-low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ A.output)
```

来源行 34
```agda
  raw-low : (e : SI.E.HC A.target) → SI.E.tree e ≼ K.readRW (proj₁ A.output)
```

来源行 38
```agda
at-one : (t : E.T) (out : ℕ → O.Tr⁺ B.zero) (v : O.Tr⁺ B.zero) → v ≡ out 1
  → ((e : SI.E.HC t) → SI.E.tree e ≼ K.readRW (proj₁ v))
  → Σ ℕ λ q → (e : SI.E.HC t) → SI.E.tree e ≼ K.readRW (proj₁ (out q))
```

## probes/OCF/Lean/YiE4Inner.lagda.md

来源行 20
```agda
shift-ctx : (h h′ : B.L) (eq : h ≡ h′) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
  → (h , o , r , bs) ≡ (h′ , subst P.Ok eq o , subst TB.Rb eq r , subst F.Base eq bs)
```

来源行 23
```agda
module Inner (k : B.L) (a : B.Tr k → B.L) (o : P.Ok (B.nd (B.sΩ k) a))
  (r : TB.Rb (B.nd (B.sΩ k) a)) (bs : F.Base (B.nd (B.sΩ k) a)) (β : O.Tr⁺ B.zero) where
```

来源行 24
```agda
  (r : TB.Rb (B.nd (B.sΩ k) a)) (bs : F.Base (B.nd (B.sΩ k) a)) (β : O.Tr⁺ B.zero) where
```

来源行 28
```agda
    g : B.Tr k → B.Tr ℓ
```

来源行 30
```agda
    g-eq : g ≡ (λ d → proj₁ (O.upz {s = B.sΩ k} {h = a} d (O.Ωt (a d))))
```

来源行 32
```agda
    feed : B.Tr k → B.Tr k
```

来源行 34
```agda
    feed-eq : feed ≡ (λ d → proj₁ (TB.ψ ℓ o r bs k (P.ink P.self) (bs k (P.ink P.self)) (g d)))
```

来源行 36
```agda
    out : B.Tr k → O.Tr⁺ B.zero
```

来源行 38
```agda
    out-eq : out ≡ (λ d → TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) β (g d))
```

来源行 40
```agda
  chain : ℕ → B.Tr k
```

来源行 42
```agda
  two : chain 2 ≡ feed (feed B.zero)
```

来源行 47
```agda
    row : Q.collapse (ℓ , o , r , bs) β ≡ O.limc⁺ (λ n → out (chain n))
```

## probes/OCF/Lean/YiE4Instances.lagda.md

来源行 17
```agda
module Canonical (r : TB.Rb B.Λ) where
```

来源行 19
```agda
  environment : (Q.level D.ctx , Q.okay D.ctx , Q.table D.ctx , Q.base D.ctx) ≡ D.make D.c₁
```

来源行 21
```agda
  chain : D.c₁ ≡ D.c₁
```

来源行 23
```agda
  beta : D.β ≡ D.β
```

来源行 25
```agda
  hc : SI.E.HC A.target
```

来源行 27
```agda
  child-table : ∀ n c → D.Step.child-table n c ≡ proj₂ (proj₂ r (suc n)) c
```

## probes/OCF/Lean/YiE4Objects.lagda.md

来源行 25
```agda
  ctx : Q.Ctx
```

来源行 27
```agda
  ctx-eq : ctx ≡ Q.make C.c₁
```

来源行 29
```agda
  β : O.Tr⁺ B.zero
```

来源行 31
```agda
  β-eq : β ≡ GI.betaᴱ 3
```

来源行 35
```agda
  output : O.Tr⁺ B.zero
```

来源行 37
```agda
  output-eq : output ≡ Q.collapse ctx β
```

来源行 41
```agda
  target : E.T
```

来源行 43
```agda
  target-eq : target ≡ LS.target
```

来源行 47
```agda
  hc : SI.E.HC target
```

来源行 49
```agda
  reference : SI.E.HC target → L.Ordᶜ L.zero
```

来源行 51
```agda
  reference-eq : ∀ h → reference h ≡ SI.E.tree h
```

## probes/OCF/Lean/YiE4Param.lagda.md

来源行 2
```agda
验收工程副本；pre、底、起点、Step 与限制底按 r : Rb Λ 参数化。
```

来源行 16
```agda
module At (r : TB.Rb B.Λ) where
  table : ∀ n → TB.Rb (B.tw n)
```

来源行 17
```agda
  table : ∀ n → TB.Rb (B.tw n)
```

来源行 21
```agda
    FΛ : ℕ → B.Tr B.Λ
```

来源行 23
```agda
    FΛ-eq : ∀ n → FΛ n ≡ proj₁ (O.upz {s = B.sL} {h = B.tw} n (O.Ωt (B.tw n)))
```

来源行 25
```agda
    pre : ℕ → B.Tr B.Λ
```

来源行 28
```agda
    pre-zero : pre 0 ≡ B.zero
```

来源行 30
```agda
    pre-suc : ∀ n → pre (suc n) ≡ O.cum FΛ n
```

来源行 32
```agda
    baseᴱ : ∀ n → F.Base (B.tw n)
```

来源行 34
```agda
    baseᴱ-eq : ∀ n → baseᴱ n ≡ (λ i u → TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) (pre n))
```

来源行 36
```agda
    betaᴱ : (n : ℕ) → O.Tr⁺ B.zero
```

来源行 38
```agda
    betaᴱ-eq : ∀ n → betaᴱ n ≡ TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (pre n)
```

来源行 40
```agda
  module Step (n : ℕ) where
```

来源行 43
```agda
    child : B.Tr k → B.L
```

来源行 45
```agda
    child-table : ∀ c → TB.Rb (child c)
```

来源行 49
```agda
      g : B.Tr k → B.Tr ℓ
```

来源行 51
```agda
      g-eq : g ≡ (λ c → proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c))))
```

来源行 53
```agda
      feed : B.Tr k → B.Tr k
```

来源行 56
```agda
      feed-eq : feed ≡ (λ c → proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) k (P.ink P.self)
        (baseᴱ (suc n) k (P.ink P.self)) (g c)))
```

来源行 59
```agda
      out : B.Tr k → O.Tr⁺ B.zero
```

来源行 61
```agda
      out-eq : out ≡ (λ c → TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c))
```

来源行 63
```agda
      out-child : ∀ c → out c ≡ TB.ψ (child c) (proj₂ (P.Ok-tw (suc n)) c) (child-table c)
        (λ i u → baseᴱ (suc n) i (P.inc c u)) B.zero (P.z≤ (child c)) (betaᴱ (suc n)) (proj₁ (O.Ωt (child c)))
```

来源行 66
```agda
    chain : ℕ → B.Tr k
```

来源行 68
```agda
    chain-zero : chain 0 ≡ B.zero
```

来源行 70
```agda
    chain-step : ∀ q → chain (suc q) ≡ feed (chain q)
```

来源行 74
```agda
    restricted : ∀ c → F.Base (Step.child 2 c)
```

来源行 76
```agda
    restricted-eq : ∀ c → restricted c ≡ (λ i u → baseᴱ 3 i (P.inc c u))
```

来源行 78
```agda
  make : B.Tr (B.tw 2) → Q.Ctx
```

来源行 82
```agda
    c₁ : B.Tr (B.tw 2)
```

来源行 84
```agda
    c₁-eq : c₁ ≡ Step.chain 2 1
```

来源行 86
```agda
    ctx : Q.Ctx
```

来源行 88
```agda
    ctx-eq : ctx ≡ make c₁
```

来源行 90
```agda
    β : O.Tr⁺ B.zero
```

来源行 92
```agda
    β-eq : β ≡ betaᴱ 3
```

来源行 96
```agda
    output : O.Tr⁺ B.zero
```

来源行 98
```agda
    output-eq : output ≡ Q.collapse ctx β
```

## probes/OCF/Lean/YiE4ParamFrame.lagda.md

来源行 24
```agda
module For (r : TB.Rb B.Λ) where
```

来源行 27
```agda
  module Frame (c : B.Tr (B.tw 2)) (c-eq : c ≡ D.c₁)
    (h : B.L) (o : P.Ok h) (rr : TB.Rb h) (bs : F.Base h)
    (env-eq : (h , o , rr , bs) ≡ D.make c)
    (β : O.Tr⁺ B.zero) (β-eq : β ≡ D.β)
    (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , rr , bs) β))) where
    context-eq : (h , o , rr , bs) ≡ D.ctx
```

来源行 28
```agda
    (h : B.L) (o : P.Ok h) (rr : TB.Rb h) (bs : F.Base h)
```

来源行 29
```agda
    (env-eq : (h , o , rr , bs) ≡ D.make c)
```

来源行 30
```agda
    (β : O.Tr⁺ B.zero) (β-eq : β ≡ D.β)
```

来源行 31
```agda
    (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , rr , bs) β))) where
```

来源行 32
```agda
    context-eq : (h , o , rr , bs) ≡ D.ctx
```

来源行 34
```agda
    sealed-low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ D.output)
```

来源行 37
```agda
    raw-low : (e : SI.E.HC A.target) → SI.E.tree e ≼ K.readRW (proj₁ D.output)
```

来源行 42
```agda
    collapse-wire : ∀ c → Q.collapse (D.make c) (D.betaᴱ 3) ≡ D.Step.out 2 c
```

来源行 46
```agda
    output-chain : D.output ≡ D.Step.out 2 (D.Step.chain 2 1)
```

来源行 49
```agda
  Missing : Set
```

来源行 50
```agda
  Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))
```

来源行 51
```agda
  FirstAt : Set
```

来源行 52
```agda
  FirstAt = Σ ℕ λ q → (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ (D.Step.out 2 (D.Step.chain 2 q)))
```

来源行 53
```agda
  module Use (low : Missing) where
    -- perf: C-9，唯一规范实例，所有环境等式由定义规格实填。
```

来源行 56
```agda
    target-low : (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ D.output)
```

来源行 59
```agda
    first-at-one : FirstAt
```

## probes/OCF/Lean/YiE4ParamInner.lagda.md

来源行 19
```agda
module At (r : TB.Rb B.Λ) where
```

来源行 24
```agda
    base₀ : F.Base k
```

来源行 26
```agda
    base₀-eq : base₀ ≡ D.restricted B.zero
```

来源行 28
```agda
    branch : B.Tr (B.tw 1) → B.Tr k
```

来源行 31
```agda
    branch-eq : branch ≡ (λ d → proj₁ (TB.ψ k (P.Ok-tw 2) (D.Step.child-table 2 B.zero) base₀ k P.self
      (D.baseᴱ 3 k (P.ink P.self)) (D.Step.g 1 d)))
```

来源行 34
```agda
  a : B.Tr (B.tw 1) → B.L
```

来源行 40
```agda
    c₁-shape : D.c₁ ≡ B.Ω (inj₁ (inj₁ tt)) branch
```

来源行 42
```agda
  h-eq : D.Step.child 2 D.c₁ ≡ h
```

来源行 46
```agda
    o : P.Ok h
```

来源行 48
```agda
    rr : TB.Rb h
```

来源行 50
```agda
    base₁ : F.Base h
```

来源行 52
```agda
    base₁-eq : base₁ ≡ subst F.Base h-eq (D.restricted D.c₁)
```

来源行 54
```agda
    ctx-shape : D.make D.c₁ ≡ (h , o , rr , base₁)
```

来源行 59
```agda
  first-row : D.output ≡ O.limc⁺ (λ n → Inner.out (Inner.chain n))
```

## probes/OCF/Lean/YiE4Use.lagda.md

来源行 25
```agda
collapse-wire : ∀ c → Q.collapse (Q.make c) (GI.betaᴱ 3) ≡ FR.Step.out 2 c
```

来源行 31
```agda
  output-actual : A.output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
```

来源行 34
```agda
Missing : Set
```

来源行 35
```agda
Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse A.ctx A.β))
```

来源行 37
```agda
module Use (low : Missing) where
  -- perf: C-9，层号、合法性、表和底由同一个规范环境给出，Σ 的 η 不展开折叠。
```

来源行 41
```agda
  target-low : (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ A.output)
```

来源行 44
```agda
  first-at-one : FR.FirstMissing
```
