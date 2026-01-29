| name | description |
|------|-------------|
| wiggum-ideas | Generate 30-50 task ideas through systematic workflow combining codebase analysis with market research. Produces improvements, features, bug fixes, refactors, and innovative exploratory tasks. Always creates kanban tasks. |

# Wiggum Ideas

## Purpose

Generate a comprehensive batch of **30-50 task ideas** through systematic exploration that combines high-level codebase analysis with market research. Each session produces a diverse mix of improvements, new features, bug fixes, unimplemented features, refactors, and innovative exploratory ideas. All ideas are automatically added to the kanban.

## Input

Optional focus area (e.g., "performance", "security", "user experience", "competitive features").

## Output

**30-50 kanban tasks** including:
- Bug fixes and unimplemented features discovered during analysis
- Improvements to existing functionality
- New features based on market research
- Refactoring opportunities
- **3-5 innovative, exploratory ideas** that push boundaries

## Critical Rules

1. **Research before suggesting** - Base ideas on findings from codebase and market research
2. **First principles analysis** - Evaluate every finding from first principles, not just pattern matching
3. **Volume target: 30-50 tasks** - Each session should produce substantial, actionable output
4. **Always create kanban tasks** - Don't ask for selection; add all discovered ideas to kanban
5. **Medium to medium-large task sizing** - Tasks should be substantial but achievable
6. **Include innovative ideas** - Every batch must include 3-5 exploratory/outside-the-box tasks

## Task Sizing Guidelines

Tasks should be **medium to medium-large** in scope:

**Good task sizes:**
- Moving a component from local to cloud-based architecture
- Adding middleware for cross-cutting concerns
- Implementing a caching layer
- Building a new API subsystem
- Refactoring a module to support new patterns
- Adding comprehensive monitoring to a service

**Too small (avoid):**
- Fix a single typo
- Add one validation check
- Rename a variable

**Too large (avoid):**
- Complete system rewrite
- Migrate entire codebase to new language
- Full infrastructure overhaul

## Core Workflow: 5 Phases

### Phase 1: Discovery Questions

**Goal:** Understand the project vision and constraints through product and technical questions.

**Questions to ask:**

```yaml
questions:
  - question: What is the overall product vision and target audience?
    header: Vision
    multiSelect: false
    options:
      - label: B2B Enterprise
        description: Business customers, compliance, integrations
      - label: B2C Consumer
        description: Individual users, scale, user experience
      - label: Developer Tools
        description: Developers, DX, documentation, APIs
      - label: Internal Platform
        description: Internal teams, reliability, efficiency
```

```yaml
questions:
  - question: What scale are you targeting?
    header: Scale
    multiSelect: false
    options:
      - label: Startup/MVP
        description: Fast iteration, validate ideas quickly
      - label: Growth stage
        description: Scaling users, building foundations
      - label: Enterprise scale
        description: High availability, compliance, performance
```

```yaml
questions:
  - question: What areas need the most attention architecturally?
    header: Architecture
    multiSelect: true
    options:
      - label: API design
        description: Endpoints, contracts, versioning
      - label: Data layer
        description: Storage, caching, consistency
      - label: Infrastructure
        description: Deployment, scaling, observability
      - label: Security
        description: Auth, authorization, data protection
```

```yaml
questions:
  - question: What are the main product improvement priorities?
    header: Product
    multiSelect: true
    options:
      - label: New features
        description: Expand capabilities for users
      - label: Performance
        description: Speed, responsiveness, efficiency
      - label: Reliability
        description: Uptime, error handling, recovery
      - label: Developer experience
        description: APIs, documentation, tooling
```

**Output:** Clear understanding of vision, scale, architecture focus, and product priorities.

---

### Phase 2: Parallel Exploration

**Goal:** Analyze codebase and research market simultaneously to find opportunities.

#### Dimension A: Codebase Analysis

Explore the codebase at a high level to identify:

- **Improvements**: Areas where existing functionality could work better
- **Bug fixes**: Issues, edge cases, or error-prone patterns
- **Unimplemented features**: TODOs, partial implementations, missing functionality
- **Refactoring opportunities**: Code that could be restructured for maintainability
- **Architectural gaps**: Missing layers, inconsistent patterns, scaling limitations

Focus on understanding the system holistically rather than line-by-line analysis.

#### Dimension B: Market Research

**Use the WebSearch tool** to research:

- Industry best practices and emerging patterns
- Competitor features and differentiators
- User expectations in this product category
- Security advisories and compliance requirements
- Technology trends that could provide advantages

**What to look for:**
- Features users expect but are missing
- Industry standards the project should meet
- Innovative approaches competitors are using
- Emerging technologies that could differentiate

#### Dimension C: Pattern Review

- What patterns exist that could be extended project-wide?
- What patterns are inconsistently applied?
- What modern alternatives exist for legacy approaches?
- Where could new architectural patterns unlock capabilities?

**Output:** Raw findings from all three dimensions.

---

### Phase 3: First Principles Analysis

**Goal:** Analyze findings using first principles to produce high-quality task ideas.

**First principles approach:**
1. **Identify the core problem** - What is the fundamental issue or opportunity?
2. **Question assumptions** - Why is it done this way? Must it be?
3. **Break down to fundamentals** - What are the basic truths here?
4. **Rebuild from ground up** - What solution makes sense from first principles?
5. **Consider second-order effects** - What would this change enable or break?

**For each finding, determine:**
- Is this a real problem or just a perceived one?
- What is the root cause, not just the symptom?
- What is the simplest solution that addresses the fundamental issue?
- Is there a more innovative approach we're not considering?

**Scoring (70+ to include):**

| Score | Level | Criteria |
|-------|-------|----------|
| 90-100 | Very High | Clear evidence, obvious improvement |
| 80-89 | High | Strong evidence, well-understood opportunity |
| 70-79 | Medium | Moderate evidence, reasonable benefit |
| <70 | Filter | Insufficient evidence, don't include |

**Output:** Analyzed findings with confidence scores.

---

### Phase 4: Generate Task Batch

**Goal:** Produce 30-50 diverse tasks including innovative ideas.

**Task distribution guidance:**
- ~40% Improvements and features
- ~25% Bug fixes and reliability
- ~20% Refactoring and tech debt
- ~10% Infrastructure and tooling
- **3-5 innovative/exploratory tasks** (mandatory)

**Innovative task ideas should:**
- Push beyond obvious improvements
- Explore new technologies or patterns
- Consider unconventional approaches
- Potentially differentiate the product
- Think about what competitors aren't doing

**For each task, document:**
- **Title**: Clear, actionable name
- **Category**: Feature / Improvement / Bug Fix / Refactor / Infrastructure / Innovative
- **Rationale**: Evidence from exploration
- **Priority**: CRITICAL / HIGH / MEDIUM / LOW

**Output:** 30-50 categorized tasks with rationale.

---

### Phase 5: Create Kanban Tasks

**Goal:** Add all tasks to the kanban.

**Do not ask for selection.** Add all discovered tasks to `.ralph/kanban.md` using the proper task format:

```markdown
- [ ] **[PREFIX-NNN]** Task title
  - Description: Detailed explanation of what needs to be done
  - Priority: HIGH
  - Dependencies: none
```

**After creating tasks:**
- Summarize what was added by category
- Highlight the innovative/exploratory tasks
- Note any patterns or themes discovered

## Example Session Flow

**User**: `/wiggum-ideas`

**Phase 1: Discovery Questions**

*[Uses AskUserQuestion about vision, scale, architecture, product priorities]*

**User answers**: B2B Enterprise, Growth stage, API design + Security, New features + Reliability

**Phase 2: Parallel Exploration**

**Dimension A - Codebase findings:**
- Found partial webhook implementation that was never completed
- Authentication module handles basic cases but lacks enterprise SSO
- Several endpoints missing proper error responses
- Logging is inconsistent across services
- No retry logic for external service calls
- Database queries could be optimized in reporting module
- Configuration scattered across multiple files
- Missing API versioning strategy
- Test coverage gaps in payment processing
- No rate limiting on public endpoints

**Dimension B - Market research (using WebSearch):**
- Enterprise customers expect audit logging
- Competitors offering GraphQL alongside REST
- Industry moving toward event-driven architectures
- SOC2 compliance becoming table stakes
- AI-assisted features emerging as differentiator

**Dimension C - Pattern review:**
- Error handling pattern exists but not universally applied
- Could extend caching pattern from user service to others
- Middleware approach could centralize cross-cutting concerns

**Phase 3: First Principles Analysis**

Applying first principles to each finding:
- Webhook implementation: Core need is reliable event delivery, not just webhooks
- SSO: Enterprise identity is about trust delegation, consider broader auth strategy
- [continues for all findings...]

**Phase 4: Generate Task Batch**

*[Generates 35+ tasks across all categories]*

Sample tasks:
1. Implement complete webhook delivery system with retry logic
2. Add enterprise SSO support (SAML, OIDC)
3. Create unified error response middleware
4. Implement structured audit logging for compliance
5. Add API versioning strategy and v2 endpoints
...
[30 more standard tasks]
...
33. **[Innovative]** Explore event sourcing for audit trail
34. **[Innovative]** Prototype AI-assisted query builder
35. **[Innovative]** Investigate GraphQL federation for microservices
36. **[Innovative]** Research edge computing for latency-sensitive operations

**Phase 5: Create Kanban Tasks**

*[Adds all 36 tasks to .ralph/kanban.md]*

**Summary:**
- Added 36 new tasks to kanban
- 12 Feature tasks
- 8 Improvement tasks
- 6 Bug fix tasks
- 6 Refactor tasks
- 4 Innovative/exploratory tasks

**Innovative highlights:**
- Event sourcing exploration could transform audit capabilities
- AI-assisted features align with industry direction
- GraphQL federation worth investigating as we grow microservices

## Key Principles

1. **Volume matters** - Produce 30-50 tasks, not 3-5
2. **First principles** - Analyze from fundamentals, don't just pattern match
3. **Always create tasks** - Never ask for selection, add everything to kanban
4. **Use WebSearch** - Market research requires actual web research
5. **Include innovation** - 3-5 tasks must be exploratory/outside-the-box
6. **Right-size tasks** - Medium to medium-large, not trivial or epic
7. **Product + Technical** - Questions span both perspectives

## Reference Documents

- **Categorization patterns**: references/categorization-patterns.md
