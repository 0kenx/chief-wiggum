# Cost and Time Tracking Implementation

This document describes the cost and time tracking features added to Chief Wiggum workers.

## Overview

Each worker run now tracks:
- **Time spent**: Total execution time from start to finish
- **API cost**: Estimated cost based on Claude Sonnet 4.5 pricing (2026)
- **Token usage**: Detailed breakdown of input, output, cache creation, and cache read tokens

## Implementation Details

### Files Modified

1. **lib/calculate-cost.sh** (new)
   - Parses worker.log files to extract token usage from JSON output
   - Calculates time spent using timestamp markers
   - Computes cost based on current Claude API pricing
   - Exports metrics as environment variables for use in PR summaries

2. **lib/ralph-loop.sh**
   - Added `WORKER_START_TIME` timestamp marker at loop start (line 17-18)
   - Added `WORKER_END_TIME` timestamp marker at loop end (line 131-132)
   - These markers enable accurate time tracking

3. **lib/worker.sh**
   - Sources the calculate-cost.sh script (line 15)
   - Calls cost calculation before creating PR (line 205)
   - Includes metrics section in PR body (lines 208-220)

### Cost Calculation Method

The script uses the following Claude Sonnet 4.5 pricing (as of 2026):

| Token Type | Price per Million Tokens |
|-----------|-------------------------|
| Input tokens | $3.00 |
| Output tokens | $15.00 |
| Cache creation tokens | $3.00 |
| Cache read tokens | $0.30 (10% of input) |

**Formula:**
```
Total Cost = (input_tokens × $3.00 / 1M) +
             (output_tokens × $15.00 / 1M) +
             (cache_creation_tokens × $3.00 / 1M) +
             (cache_read_tokens × $0.30 / 1M)
```

### Time Tracking Method

Time is calculated using one of these methods (in order of preference):

1. **Timestamp markers**: `WORKER_START_TIME` and `WORKER_END_TIME` markers in log
2. **File timestamps**: Creation and modification times of worker.log
3. **Iteration estimate**: Number of iterations × 30 seconds (fallback)

### PR Summary Format

The metrics are included in the PR body as follows:

```markdown
## Metrics

**Time Spent:** HH:MM:SS
**API Cost:** $X.XXXXXX (Sonnet 4.5)

**Token Usage:**
- Input: XXX,XXX tokens
- Output: XXX,XXX tokens
- Cache creation: XXX,XXX tokens
- Cache read: XXX,XXX tokens
```

## Usage

### Manual Cost Calculation

To manually calculate costs for a worker run:

```bash
bash lib/calculate-cost.sh /path/to/worker.log
```

### Automatic Integration

The cost calculation is automatically performed during worker cleanup when creating PRs. No manual intervention required.

## Example Output

```
=== Worker Time and Cost Report ===

Time Spent: 00:06:00 (360 seconds)

Token Usage:
  Input tokens: 294
  Output tokens: 6,163
  Cache creation tokens: 188,344
  Cache read tokens: 1,205,070
  Total tokens: 1,399,871

Cost Breakdown (Claude Sonnet 4.5):
  Input tokens: $0.000882
  Output tokens: $0.092445
  Cache creation: $0.565032
  Cache read: $0.361521
  Total cost: $1.019880
```

## References

- [Claude API Pricing (2026)](https://platform.claude.com/docs/en/about-claude/pricing)
- [Claude API Cost Calculator](https://costgoat.com/pricing/claude-api)
- [Claude Code Pricing Guide](https://blog.promptlayer.com/claude-code-pricing-how-to-save-money/)

## Cumulative Metrics (Multi-Worker Sessions)

Starting from the aggregation feature, Chief Wiggum now collects and reports cumulative metrics across all workers when `wiggum run` completes.

### Aggregate Metrics Report

When all tasks are complete, `wiggum run` automatically:
1. Aggregates cost/time across all workers
2. Calculates total tokens, costs, and duration
3. Generates a summary report on completion
4. Exports metrics to `.ralph/metrics.json`

### Files Added

**lib/aggregate-metrics.sh** (new)
- Scans all worker directories in `.ralph/workers/`
- Aggregates metrics from each worker's log file
- Calculates totals and averages
- Generates both human-readable report and JSON export
- Tracks worker success/failure rates

### Cumulative Report Format

```
==========================================
=== Cumulative Metrics Report ===
==========================================

Workers:
  Total workers: 19
  Successful: 11
  Failed: 5
  Success rate: 57.89%

Time:
  Total time: 00:06:00 (360 seconds)
  Average per worker: 00:00:18

Tokens:
  Input tokens: 61,462
  Output tokens: 210,722
  Cache creation: 3,556,545
  Cache read: 33,131,701
  Total tokens: 36,960,430

Cost Breakdown (Claude Sonnet 4.5):
  Input tokens: $0.184386
  Output tokens: $3.160830
  Cache creation: $10.669635
  Cache read: $9.939510
  Total cost: $23.954352

==========================================
```

### JSON Export Format

The `.ralph/metrics.json` file contains:

```json
{
  "summary": {
    "total_workers": 19,
    "successful_workers": 11,
    "failed_workers": 5,
    "success_rate": 57.89,
    "total_time": "00:06:00",
    "total_time_seconds": 360,
    "total_cost": 23.954352
  },
  "tokens": {
    "input": 61462,
    "output": 210722,
    "cache_creation": 3556545,
    "cache_read": 33131701,
    "total": 36960430
  },
  "cost_breakdown": {
    "input": 0.184386,
    "output": 3.160830,
    "cache_creation": 10.669635,
    "cache_read": 9.939510,
    "total": 23.954352
  },
  "workers": [
    {
      "worker_id": "worker-TASK-001-12345",
      "status": "success",
      "time_spent": "00:01:30",
      "time_seconds": 90,
      "tokens": {
        "input": 500,
        "output": 2000,
        "cache_creation": 10000,
        "cache_read": 50000,
        "total": 62500
      },
      "cost": 1.234567,
      "pr_url": "https://github.com/user/repo/pull/123"
    }
  ]
}
```

### Manual Aggregation

To manually aggregate metrics without running all workers:

```bash
bash lib/aggregate-metrics.sh .ralph
```

Or to specify a custom output path:

```bash
bash lib/aggregate-metrics.sh .ralph /custom/path/metrics.json
```

### Integration with wiggum run

The aggregation is automatically triggered when `wiggum run` completes all tasks:

1. All workers finish (or fail)
2. Metrics are aggregated from `.ralph/workers/*/worker.log`
3. Summary report is displayed to console
4. JSON is exported to `.ralph/metrics.json`
5. Final summary includes link to metrics file

## Future Enhancements

Potential improvements:
1. Add cost tracking to changelog entries
2. Add budget alerts/warnings
3. Support different model pricing (Haiku, Opus)
4. Track cost trends over time
5. Add metrics visualization dashboard
