# 定义与定理逐字表
仅 Base、Objects 通过；“编译定理”表示本路临时文件初次冷编 0，尚待主审独立冷编。

## YiE3Base（通过）

### Ctx
文件：`YiE3Base.agda`；档：已检查定义。将孩子层号、合法性、比较表与实际底合在一个依赖环境。
```agda
Ctx : Set
```

### level
文件：`YiE3Base.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
level : Ctx → B.L
```

### okay
文件：`YiE3Base.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
okay : (d : Ctx) → P.Ok (level d)
```

### table
文件：`YiE3Base.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
table : (d : Ctx) → TB.Rb (level d)
```

### base
文件：`YiE3Base.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
base : (d : Ctx) → F.Base (level d)
```

### collapse
文件：`YiE3Base.agda`；档：已检查定义。在变量环境中将该层 Ω 树折到零层。
```agda
collapse : Ctx → O.Tr⁺ B.zero → O.Tr⁺ B.zero
```

### make
文件：`YiE3Base.agda`；档：已检查定义。以外层链点构造原第 3 站的实际限制环境。
```agda
make : B.Tr (B.tw 2) → Ctx
```

### raw-wire
文件：`YiE3Base.agda`；档：编译定理。变量链编号上的原输出接线；复用 YiLBActual.out-child。
```agda
raw-wire : ∀ q → collapse (make (FR.Step.chain 2 q)) (GI.betaᴱ 3)
  ≡ FR.Step.out 2 (FR.Step.chain 2 q)
```

### iter-two
文件：`YiE3Base.agda`；档：编译定理。函数变量上的第二次迭代等式。
```agda
iter-two : {A : Set} (f : A → A) (z : A) → O.iter f z 2 ≡ f (f z)
```

## YiE3Objects（通过）

### c₁
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  c₁ : B.Tr (B.tw 2)
```

### c₁-def
文件：`YiE3Objects.agda`；档：编译定理。封装对象确为原 Step 2 的链点 1。
```agda
  c₁-def : c₁ ≡ FR.Step.chain 2 1
```

### base₀
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  base₀ : F.Base (B.tw 2)
```

### base₀-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  base₀-def : base₀ ≡ (λ i u → GI.baseᴱ 3 i (P.inc B.zero u))
```

### branch
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  branch : B.Tr (B.tw 1) → B.Tr (B.tw 2)
```

### branch-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  branch-def : branch ≡ (λ d → proj₁ (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) base₀
    (B.tw 2) P.self (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (FR.Step.g 1 d)))
```

### c₁-shape
文件：`YiE3Objects.agda`；档：编译定理。原链点 1 的 Ω 形状。
```agda
  c₁-shape : c₁ ≡ B.Ω (inj₁ (inj₁ tt)) branch
```

### ctx
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  ctx : Q.Ctx
```

### ctx-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  ctx-def : ctx ≡ Q.make c₁
```

### h₁
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  h₁ : B.L
```

### h₁-def
文件：`YiE3Objects.agda`；档：编译定理。封装层号确为原链点的孩子层号。
```agda
  h₁-def : h₁ ≡ FR.Step.child 2 c₁
```

### o₁
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  o₁ : P.Ok h₁
```

### o₁-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  o₁-def : subst P.Ok h₁-def o₁ ≡ proj₂ (P.Ok-tw 3) c₁
```

### r₁
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  r₁ : TB.Rb h₁
```

### r₁-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  r₁-def : subst TB.Rb h₁-def r₁ ≡ MT.rbᶻ (FR.Step.child 2 c₁)
```

### base₁
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  base₁ : F.Base h₁
```

### base₁-def
文件：`YiE3Objects.agda`；档：编译定理。封装底沿层号等式输运后恰为原 baseᴱ 3 沿 inc c₁ 的限制。
```agda
  base₁-def : subst F.Base h₁-def base₁ ≡ (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
```

### a
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  a : B.Tr (B.tw 1) → B.L
```

### a-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  a-def : a ≡ (λ d → B.tw 2 B.⊕ B.↑ (B.tw 2) (branch d))
```

### h₁-shape
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  h₁-shape : h₁ ≡ B.nd (B.sΩ (B.tw 1)) a
```

### β
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  β : O.Tr⁺ B.zero
```

### β-def
文件：`YiE3Objects.agda`；档：编译定理。起点仍为实际继承的 betaᴱ 3。
```agda
  β-def : β ≡ GI.betaᴱ 3
```

### output
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  output : O.Tr⁺ B.zero
```

### output-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  output-def : output ≡ Q.collapse ctx β
```

### output-actual
文件：`YiE3Objects.agda`；档：编译定理。封装输出恰为原链点 1 的输出，实际底与起点均未替换。
```agda
  output-actual : output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
```

### target
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  target : E.T
```

### target-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  target-def : target ≡ LS.target
```

### hc
文件：`YiE3Objects.agda`；档：编译定理。原目标的封装 HC 闭项。
```agda
  hc : SI.E.HC target
```

### hc-def
文件：`YiE3Objects.agda`；档：编译定理。定义等式或类型按源码逐字给出。
```agda
  hc-def : hc ≡ subst SI.E.HC (sym target-def) LS.hc-target
```

### reference
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  reference : SI.E.HC target → L.Ordᶜ L.zero
```

### reference-def
文件：`YiE3Objects.agda`；档：编译定理。参照族逐个证书的值与 SI.E.tree 一致。
```agda
  reference-def : ∀ h → reference h ≡ SI.E.tree h
```

### target-tree
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  target-tree : L.Ordᶜ L.zero
```

### target-tree-def
文件：`YiE3Objects.agda`；档：编译定理。封装闭参照树由封装 HC 的参照族值给出。
```agda
  target-tree-def : target-tree ≡ reference hc
```

### slot
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  slot : B.tw 1 P.≤ h₁
```

### slot-def
文件：`YiE3Objects.agda`；档：编译定理。内层槽位路径由实际孩子的 Ω 形状等式输运。
```agda
  slot-def : slot ≡ subst (λ h → B.tw 1 P.≤ h) (sym h₁-shape) (P.ink P.self)
```

### inner-g
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  inner-g : B.Tr (B.tw 1) → B.Tr h₁
```

### inner-g-def
文件：`YiE3Objects.agda`；档：编译定理。内层分支树由该形状等式输运回实际孩子层号。
```agda
  inner-g-def : ∀ d → inner-g d ≡ subst B.Tr (sym h₁-shape)
    (proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} d (O.Ωt (a d))))
```

### inner-feed
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  inner-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
```

### inner-feed-def
文件：`YiE3Objects.agda`；档：编译定理。内层回灌使用该孩子层上的原实际限制底。
```agda
  inner-feed-def : ∀ d → inner-feed d ≡ proj₁
    (TB.ψ h₁ o₁ r₁ base₁ (B.tw 1) slot (base₁ (B.tw 1) slot) (inner-g d))
```

### inner-out
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  inner-out : B.Tr (B.tw 1) → O.Tr⁺ B.zero
```

### inner-out-def
文件：`YiE3Objects.agda`；档：编译定理。内层零目标折叠使用原实际起点。
```agda
  inner-out-def : ∀ d → inner-out d ≡ TB.ψ h₁ o₁ r₁ base₁ B.zero (P.z≤ h₁) β (inner-g d)
```

### inner-chain
文件：`YiE3Objects.agda`；档：已检查定义。定义等式或类型按源码逐字给出。
```agda
  inner-chain : ℕ → B.Tr (B.tw 1)
```

### inner-chain-def
文件：`YiE3Objects.agda`；档：编译定理。内层链从零迭代该封装回灌。
```agda
  inner-chain-def : inner-chain ≡ O.iter inner-feed B.zero
```

### inner-zero
文件：`YiE3Objects.agda`；档：编译定理。内层链第零点是零。
```agda
  inner-zero : inner-chain 0 ≡ B.zero
```

### inner-step
文件：`YiE3Objects.agda`；档：编译定理。内层链每一步由封装回灌给出。
```agda
  inner-step : ∀ n → inner-chain (suc n) ≡ inner-feed (inner-chain n)
```

### inner-two
文件：`YiE3Objects.agda`；档：编译定理。封装内层链的第二次迭代等式；由变量引理得到。
```agda
  inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
```

## YiE3Frame（未验收：251）

### sealed-low
文件：`YiE3Frame.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  sealed-low : (h : SI.E.HC A.target) → A.reference h ≼ K.readRW (proj₁ A.output)
```

### raw-low
文件：`YiE3Frame.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  raw-low : (h : SI.E.HC A.target) → SI.E.tree h ≼ K.readRW (proj₁ A.output)
```

### actual-low
文件：`YiE3Frame.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  actual-low : (h : SI.E.HC A.target) → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 1)))
```

### connect
文件：`YiE3Frame.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  connect : (h : SI.E.HC LS.target) → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 1)))
```

### first-at-one
文件：`YiE3Frame.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  first-at-one : FR.FirstMissing
```

## YiE3Use（未编译）

### Missing
文件：`YiE3Use.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
Missing : Set
```

### low
文件：`YiE3Use.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  low : (h : SI.E.HC A.target) → A.reference h ≼ K.readRW (proj₁ (Q.collapse A.ctx A.β))
```

### first
文件：`YiE3Use.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  first : FR.FirstMissing
```

### first-at-one
文件：`YiE3Use.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
first-at-one : Missing → FR.FirstMissing
```

## YiE3TwoSealed（未编译）

### base₁
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
base₁ : F.Base h₁
```

### base₀
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
base₀ : F.Base k
```

### branch
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
branch : B.Tr (B.tw 1) → B.Tr k
```

### a
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
a : B.Tr (B.tw 1) → B.L
```

### c₁-shape
文件：`YiE3TwoSealed.agda`；档：未验收陈述。原链点 1 的 Ω 形状。
```agda
c₁-shape : c₁ ≡ B.Ω (inj₁ (inj₁ tt)) branch
```

### h₁-shape
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
h₁-shape : h₁ ≡ B.nd (B.sΩ (B.tw 1)) a
```

### inner-g
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
inner-g : B.Tr (B.tw 1) → B.Tr h₁
```

### inner-feed
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
inner-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
```

### inner-chain
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
inner-chain : ℕ → B.Tr (B.tw 1)
```

### inner-out
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
inner-out : B.Tr (B.tw 1) → O.Tr⁺ B.zero
```

### inner-zero
文件：`YiE3TwoSealed.agda`；档：未验收陈述。内层链第零点是零。
```agda
inner-zero : inner-chain 0 ≡ B.zero
```

### inner-one
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
inner-one : inner-chain 1 ≡ proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁
  (B.tw 1) (P.ink P.self) (base₁ (B.tw 1) (P.ink P.self))
  (proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} B.zero (O.Ωt (a B.zero)))))
```

### sealed-feed
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  sealed-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
```

### sealed-feed-def
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  sealed-feed-def : sealed-feed ≡ inner-feed
```

### sealed-two
文件：`YiE3TwoSealed.agda`；档：未验收陈述。定义等式或类型按源码逐字给出。
```agda
  sealed-two : O.iter sealed-feed B.zero 2 ≡ sealed-feed (sealed-feed B.zero)
```

### inner-two
文件：`YiE3TwoSealed.agda`；档：未验收陈述。封装内层链的第二次迭代等式；由变量引理得到。
```agda
inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
```
