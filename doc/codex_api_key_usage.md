# Ark API Batch Usage

Ark DeepSeek/GLM API 由统一 profile 管理：

```text
config/ark_api/profiles.json
```

profile 字段：

```json
{
  "agent": "claude",
  "api_key": "...",
  "base_url": "...",
  "model": "..."
}
```

## Config Names

Claude wrapper：

```text
ark-1-deepseek
ark-1-glm
ark-2-deepseek
ark-2-glm
ark-3-deepseek
ark-3-glm
ark-4-deepseek
ark-4-glm
ark-5-deepseek
ark-5-glm
```

Codex wrapper：

```text
codex-ark-1-deepseek
codex-ark-1-glm
codex-ark-2-deepseek
codex-ark-2-glm
codex-ark-3-deepseek
codex-ark-3-glm
codex-ark-4-deepseek
codex-ark-4-glm
codex-ark-5-deepseek
codex-ark-5-glm
```

OpenCode wrapper：

```text
opencode-ark-1-deepseek
opencode-ark-1-glm
opencode-ark-2-deepseek
opencode-ark-2-glm
opencode-ark-3-deepseek
opencode-ark-3-glm
opencode-ark-4-deepseek
opencode-ark-4-glm
opencode-ark-5-deepseek
opencode-ark-5-glm
```

## Verify

```bash
scripts/batch_safe_verify.sh codex-ark-2-deepseek p003_below_zero
scripts/batch_safe_verify.sh opencode-ark-2-glm p034_unique
scripts/batch_safe_verify.sh ark-1-deepseek p014_all_prefixes
```

## Proof

```bash
scripts/batch_safe_proof.sh codex-ark-2-deepseek p007_filter_by_substring
scripts/batch_safe_proof.sh opencode-ark-4-glm p012_longest
scripts/batch_safe_proof.sh ark-3-deepseek p028_concatenate
```

## Pipeline

```bash
scripts/batch_safe_pipeline.sh codex-ark-2-deepseek p014_all_prefixes
scripts/batch_safe_pipeline.sh opencode-ark-2-glm p014_all_prefixes
scripts/batch_safe_pipeline.sh ark-1-glm p029_filter_by_prefix
```

## Results

Verify 结果：

```text
results/claude/<model>/api/
results/codex/<model>/api/
results/opencode/<model>/api/
```

Proof 结果：

```text
proof_results/claude/<model>/api/
proof_results/codex/<model>/api/
proof_results/opencode/<model>/api/
```

Pipeline 结果：

```text
pipeline_results/claude/<model>/api/
pipeline_results/codex/<model>/api/
pipeline_results/opencode/<model>/api/
```

`<model>` 当前主要是：

```text
deepseek-v4-pro
glm-5.2
```

## OpenCode Artifacts

OpenCode 每次运行都会使用该次 workspace 的隔离 XDG 目录。
runner 会把 OpenCode run-local data/config/state/cache 产物复制到：

```text
<result>/logs/opencode_artifacts/
```

认证文件 `auth.json` 会在 wrapper 退出时删除；复制产物前也会删除并跳过
`auth.json`。
