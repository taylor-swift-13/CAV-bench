# Mode: Proof-only

本附录只在 runner / 外层确定性路由已经选择 proof-only 并在 prompt 顶部标 `Mode: proof-only` 时生效。

## 触发条件

满足以下确定性路由条件时，runner 才应进入本模式：

- verify 开始的第一次 symexec 已在当前 QCP Coq mirror 生成正确完整的 VC 产物：`<name>_goal.v`、`<name>_proof_auto.v`、`<name>_proof_manual.v`、`<name>_goal_check.v`；
- runner 在 prompt 顶部显式标记 `Mode: proof-only`。

进入本模式说明：symexec 已经成功、`proof_auto.v` 也已就位，但 `proof_manual.v` 还存在未完成的手工证明义务，需要 agent 优先写真实 proof。

工具链仍按主 verify skill：使用 opam switch `qcp-8.20` / Coq 8.20.1。

## 写边界

- **不改** `input/`、`raw/`、`workspace/original/`；
- **不改**当前 QCP Coq mirror 中的 `*_goal.v`、`*_proof_auto.v`、`*_goal_check.v`；
- Target `.v` 中只允许编辑 `<name>_proof_manual.v`，且只允许把 QCP 留下的 `Admitted` 证明洞替换成真实 proof；不能为了通过检查去改 manual 中的 statement/import，也不能改其它三个 target `.v`；
- **不改 function contract**：这里的 contract 只指函数 `Require` / `Ensure` 前后条件，其中承载题意的规格不能在 verify/proof-only 阶段改弱、改题意或新增输入假设；
- 允许按主 SKILL 修改当前工作副本中的 verification annotation，包括 `Inv`、`Assert`、`Inv Assert`、`which implies`、`where`，但不能改 executable implementation；
- 可写面仍按主 SKILL：当前 QCP C mirror 中的 annotation 文件、当前 QCP Coq mirror 中的 `<name>_proof_manual.v`（及允许的本地 helper）和 mirror logs 中的 `issues.md` / `metrics.md`。

如果 generated VC 在当前 annotation 下缺少中间事实，先回 annotation 修正或加强 `Inv` / `Assert` / `Inv Assert` / `which implies` / `where`，再重跑 symexec 刷新 VC，然后证明新的 `proof_manual.v`。如果必须修改 function contract（函数 `Require` / `Ensure`）才能成立，写阻塞到 `logs/issues.md` 并退回 Contract/用户决策，不要在 proof-only 中硬改 function contract。

普通的 `proof_manual.v` 仍有未完成手工义务、`coqc` 报错、tactic 暂时失败，都不是 proof-only 退出理由。只要能继续编辑 `proof_manual.v` 或添加允许范围内的 local helper，就必须继续证明并重新编译。

proof-only 模式也必须遵守 `../skills/verify/SKILL.md` 的相关示例检索规则。应先读取同型 QCP C/annotation 示例和对应证明示例，再补全 `proof_manual.v` 并运行 `coqc`。当具体 proof theorem、`Cannot find witness`、rewrite/unification 或 tactic 失败暴露后，必须围绕该失败点到 `QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM,stdlib}/`、`SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/` 和 `SeparationLogic/stdlib/` 检索并读取相似例子；CAV 历史 workspace 只能作为补充。未基于具体失败点完成相似 proof 的检索与迁移，不得写 `Final Result: Fail`。

## 工作流仍按主 SKILL

- 本模式的第一步是读取同型具体示例和必要文档，然后基于已经生成的 VC 构造证明并编译验证；
- proof 工作按主 SKILL 的“检索相似例子/阅读必要文档 -> 修改 `proof_manual.v` -> 编译 -> 阅读第一个失败点”循环推进；若 proof 过程中确认当前 VC 在现有 annotation 下不可证，或 `coqc`/witness 失败表明当前 VC 缺少 annotation 中间事实，则必须退出 proof 循环，回到外层“写 annotation”阶段，修改 `Inv` / `Assert` / `Inv Assert` / `which implies` / `where`，并按主 SKILL 的刷新规则重跑 symexec，然后重新进入 proof 循环；
- 若返回 annotation 修改后 symexec 无法生成完整 VC，则退出 proof-only 的直接证明路径，按主 SKILL 的 verify 外层主循环重新推进：检索相似例子/阅读必要文档，修正 annotation，运行 symexec，获得有效 VC 后再进入 proof 循环；
- tactic 起手式与分离逻辑证明套路不确定时，按主 skill 规则最小读取相关 QCP proof 文档；可选路径是 `QualifiedCProgramming/.agents/skills/vc-proving/SKILL.md`、`QualifiedCProgramming/.agents/skills/vc-proving/docs/refinement-proof-tactics.md`、`QualifiedCProgramming/.agents/skills/vc-proving/docs/separation-logic-whole-proof-tactics.md`；
- attempt > 1 或 prompt 带 `Restart feedback` / `Failure feedback:` 时，优先读取反馈中的首个失败点并继续。

## 完成判据

和主 SKILL 的完成判据一致：四个 target `.v` 编译通过；`proof_manual.v` 中的手工义务都以真实证明完成；除 `proof_manual.v` 外，另外三个 target `.v` 只能由 symexec 产生，不得手改。
