# B9A · 第二次更新能否承载整棵 Y 1

请独立完成 W4 的第 4 层值证明，全程中文，模型 Opus 5.5。先读仓库根 `AGENTS.md`、工程手册 §4 及[主审指令 02](../指令-02.md)。公共目录由协调者给出；独立收到本简报时可先运行[公共准备段](00-协调简报.md)。在 `$B9_RUN/B9A` 写纯 Agda，新模块前缀 `B9Inner`。

**首交目标是 `second : Second`。** `YiLAB8Split.Second = Match (Y 1) (chainW 2)`。这要求整棵非初始 Level 链点与两次更新后的 W4 树共同满足被加项、指数的四个字段。第八批只在较小的 `X₀` 上得到配对。主审已证初态无法承载 `X₀`，本路继续向上取整棵 `Y 1`。

1. 优先试 `at1 : AtPart 1`，用 `to-second at1` 交付。`AtPart k` 使用的是第二次更新的实际**累加分支** `YiLAB9Orbit.U k`。记一次更新的状态为 c；`second-part` 给出 `U 1 ≡ ex (z 1 + c) c nc (suc (z 1)) tt`。`inner-seed` 已把 `X₀` 接到 `U 0`。先明确消费 c 的哪一处、指数的哪一处；若使用原始内链 `z 2`，补证其界到累加分支的传递。
2. `B8PairLevel.Ld-Y1/Lx-Y1` 给已满足 Level 字段的具体描述。`B8PairW4.Real-c1` 给 c 的指数描述 `lC ε = eΩ₂`，`SumR-c1` 与 `B8PairMain.shift-d` 可把 c 的被加项描述收窄到 `dΩ₂`。先试以 W4 侧的 `ex`、前缀或语义膨胀律合成同一对描述；若换描述，说明两个方向的比较。第八批 `no-merge` 否定的是一次更新的一对具体描述，本题的右端不同。
3. 如 `U 1` 太小或难以消费，可由计算选有依据的其他 k，再经 `part k` 提升；也可对整个极限给值界。不要把“在一支找齐四个字段”升格成必要条件。取得 `second` 后，分别编译 `consume second`、`consume-exp second` 对应的闭不等式，写清左右端。若有余量，优先把一个实际非初始分支接到 `LV.ψ⁰ (body (Y 1)) ≼ read WKShape.Ψ₃`，说明底族和路径；这是单独的外层目标。
4. 第二种写法可直接证明整棵 `Y 1` 在两次更新处的一个闭消费者值界。若只完成这一条，按这一条回报。任何否定也须对准签名，并给已满足的前提。新代码约 1200 行、可换一次写法；触顶或两种写法受阻时交最小未证签名与最后一个已编译实例。

在仓库根执行，按入口实名替换文件名：

```sh
agda +RTS -M6G -RTS --library-file="$B9_RUN/libraries" -i src -i probes -i "$B9_RUN/common" -i "$B9_RUN/B9A" "$B9_RUN/B9A/B9InnerMain.agda" > "$B9_RUN/B9A/compile.log" 2>&1
code=$?
echo "agda exit $code"
```

沿用公共 OPTIONS，一次一个 Agda；仓库、W4、公共源码只读。第 4 层若使用排中律或函数外延，标明条件及给出见证的具体步骤。回报按闭项、值界、否定、纸面判断分开写，列出新模块、每个分支编号、出口、退出码与依赖。源码和回报交协调者，无须等待对照路。
