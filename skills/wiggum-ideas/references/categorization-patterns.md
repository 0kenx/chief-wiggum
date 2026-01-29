# Categorization Patterns Reference

## Confidence Scoring System

Score every idea 0-100 based on evidence strength. Only present ideas scoring **70 or higher**.

### Scoring Rubric

| Score Range | Level | Criteria | Example |
|-------------|-------|----------|---------|
| 90-100 | Very High | Clear evidence in code, known issue, obvious fix | "No rate limiting on auth endpoint" |
| 80-89 | High | Strong evidence, well-understood problem | "Missing security headers" |
| 70-79 | Medium | Moderate evidence, some uncertainty | "Could benefit from caching" |
| 60-69 | Low | Weak evidence, speculative benefit | "Might improve UX" |
| <60 | Filter | Insufficient evidence | Don't present |

### Scoring Factors

**Evidence Strength (+/- 20 points)**
- Found specific code issue: +15 to +20
- Found pattern issue across files: +10 to +15
- Research indicates best practice: +5 to +10
- Theoretical concern only: -10 to -15

**Impact Clarity (+/- 15 points)**
- Clear, measurable benefit: +10 to +15
- Understood benefit, hard to measure: +5 to +10
- Vague improvement: -5 to -10

**Effort Confidence (+/- 10 points)**
- Known scope, similar work done before: +10
- Moderate uncertainty: 0
- Unknown scope, exploratory: -10

**Risk Assessment (+/- 10 points)**
- Safe, isolated change: +10
- Moderate risk, reversible: +5
- High risk, wide impact: -5 to -10

### Example Scoring

**Idea: Add rate limiting to auth endpoints**
- Evidence: Found no rate limiting in `src/routes/auth.ts` (+18)
- Impact: Prevents brute force attacks (clear benefit) (+12)
- Effort: Middleware exists, just need to apply (+8)
- Risk: Low risk, targeted change (+8)
- **Total: 96** (Very High Confidence)

**Idea: Refactor to microservices**
- Evidence: Monolith pattern found (+5)
- Impact: Better scaling (vague) (-5)
- Effort: Unknown scope (-10)
- Risk: High risk, complete rewrite (-8)
- **Total: 52** (Filter out - don't present)

## Impact/Effort Matrix

Classify every idea into one of four quadrants:

```
                    Low Effort           High Effort
                  ┌──────────────────┬──────────────────┐
                  │                  │                  │
    High Impact   │    QUICK WIN     │      MAJOR       │
                  │   Priority: 1    │   Priority: 2    │
                  │   Do these first │   Plan these     │
                  │                  │                  │
                  ├──────────────────┼──────────────────┤
                  │                  │                  │
    Low Impact    │     FILL-IN      │      AVOID       │
                  │   Priority: 3    │   Priority: 4    │
                  │   If time allows │   Skip unless    │
                  │                  │   requested      │
                  └──────────────────┴──────────────────┘
```

### Effort Guidelines

**Low Effort:**
- Single file change
- Uses existing patterns/utilities
- No new dependencies
- Familiar territory

**High Effort:**
- Multiple files across modules
- New patterns or abstractions
- New dependencies to evaluate
- Research required

### Impact Guidelines

**High Impact:**
- Security vulnerability fix
- Performance improvement (measurable)
- User-facing feature request
- Blocking issue resolution

**Low Impact:**
- Code quality improvement
- Minor UX enhancement
- Internal tooling
- Nice-to-have feature

## Category Definitions

### Quick Wins
- Impact: High
- Effort: Low
- Typical confidence: 85+
- Examples: Add validation, fix obvious bug, apply existing pattern

**Presentation format:**
```markdown
### [Title] [Confidence: N]
- **Why Quick Win**: [Brief reason]
- **Evidence**: [Specific file:line or pattern]
- **Effort**: [Why it's low effort]
```

### Features
- Impact: High
- Effort: Variable (usually Medium-High)
- Typical confidence: 75+
- Examples: New user-facing capability, major enhancement

**Presentation format:**
```markdown
### [Title] [Confidence: N]
- **User Value**: [What users get]
- **Evidence**: [Market research or user request]
- **Complexity**: [Why it needs planning]
- **Dependencies**: [Related tasks if any]
```

### Tech Debt
- Impact: Variable (usually improves maintainability)
- Effort: Variable
- Typical confidence: 80+
- Examples: Refactoring, test coverage, documentation

**Presentation format:**
```markdown
### [Title] [Confidence: N]
- **Problem**: [Current state issue]
- **Evidence**: [Specific code patterns found]
- **Benefit**: [Maintainability/reliability improvement]
```

### Security
- Impact: High (always)
- Effort: Variable
- Typical confidence: 90+ (security issues require high confidence)
- Examples: Vulnerability fix, hardening, compliance

**Presentation format:**
```markdown
### [Title] [Confidence: N]
- **Vulnerability**: [What's at risk]
- **Evidence**: [Specific finding]
- **Remediation**: [What to do]
- **Urgency**: [Critical/High/Medium]
```

### Infrastructure
- Impact: Variable (usually developer experience)
- Effort: Variable
- Typical confidence: 75+
- Examples: CI/CD, monitoring, tooling

**Presentation format:**
```markdown
### [Title] [Confidence: N]
- **Problem**: [Current pain point]
- **Solution**: [What to implement]
- **Benefit**: [DevEx/reliability improvement]
```

## Prioritization Algorithm

When presenting ideas, order by:

1. **Security issues** (always first, highest urgency)
2. **Quick Wins** (high confidence, immediate value)
3. **Blocking issues** (unblocks other work)
4. **Features** (by confidence score)
5. **Tech Debt** (by confidence score)
6. **Infrastructure** (by confidence score)
7. **Fill-ins** (only if explicitly requested)

## Anti-Patterns

### Vague Ideas
```
# Bad
"Improve performance" (no specific target)

# Good
"Add caching to user profile endpoint - found repeated database queries on every request"
```

### Unsupported Ideas
```
# Bad
"Should use GraphQL" (no evidence it would help)

# Good
"Found 15 endpoints returning unused fields - GraphQL would reduce unnecessary data transfer"
```

### Duplicate Ideas
```
# Bad
Suggesting work already in kanban

# Good
"Found TASK-022 addresses HTTPS - focusing on other security gaps"
```

### Scope Creep
```
# Bad
"Rewrite the entire auth system"

# Good
"Add rate limiting to login endpoint"
```
