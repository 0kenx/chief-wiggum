| name | description |
|------|-------------|
| wiggum-plan | Create implementation plans through systematic 7-phase workflow: discovery, exploration, clarifying questions, architecture design, plan writing, and summary. Planning only - never implements. Always writes plan to `.ralph/plans/TASK-ID.md`. |

# Wiggum Plan

## Purpose

Create implementation plans through a systematic 7-phase workflow that ensures deep codebase understanding and thoughtful architecture decisions. This skill is for **planning only** - it never implements code.

## Input

**Mode 1 - Existing Task**: A task ID from `.ralph/kanban.md` (e.g., `TASK-015`, `FEATURE-042`).

**Mode 2 - New Task**: A description of work to be done (e.g., "Add user authentication with JWT"). When no valid task ID is provided, the skill will:
1. Create the task in `.ralph/kanban.md`
2. Then create the implementation plan

## When This Skill is Invoked

**Manual invocation:**
- Before implementing a complex task
- When a task needs architectural analysis
- To document approach before handing to a worker

**From other skills:**
- After `/kanban` creates tasks that need detailed planning

## Critical Rules

1. **NEVER implement** - This skill produces plans, not code
2. **ALWAYS write the plan file** - Every session must end with writing `.ralph/plans/TASK-ID.md`
3. **Multiple iterations allowed** - Explore, ask questions, explore more as needed
4. **READ-ONLY exploration** - Only modify the kanban file (when creating tasks) and plan file
5. **Create task when needed** - If no valid task ID is provided, create the task in kanban first
6. **Clarifying questions are critical** - Never skip Phase 3; it's one of the most important phases

## Core Workflow: 7 Phases

### Phase 0: Task Creation (when no task ID provided)

**Skip this phase if a valid task ID was provided.**

When the input is a description rather than a task ID:

**Analyze existing kanban:**
- Read `.ralph/kanban.md`
- Identify the highest task number for ID assignment
- Note existing dependencies and task prefixes used
- Check for similar/related pending tasks

**Clarify requirements with AskUserQuestion:**
- Scope: What should be included/excluded?
- Priority: How urgent is this work?
- Dependencies: Does this depend on existing tasks?

**Design the task:**
- Determine if it should be one task or multiple
- If multiple tasks needed, break down with proper dependencies (use Scope field for sub-items within a single task)
- Each task should be completable by one worker in one session

**Create the task in kanban:**
- Add properly formatted task entry to `.ralph/kanban.md`
- Include all required fields: Description, Priority, Dependencies
- Use optional fields (Scope, Acceptance Criteria) when helpful
- Confirm with user before writing via AskUserQuestion

For task format details, see `/kanban` skill references:
- Task format: `skills/kanban/references/task-format.md`
- Dependency patterns: `skills/kanban/references/dependency-patterns.md`
- Sizing guidelines: `skills/kanban/references/sizing-guidelines.md`

**After task creation, continue to Phase 1 with the newly created task ID.**

---

### Phase 1: Discovery

**Goal:** Establish clarity on what needs to be built before exploring code.

**Read the task requirements:**
- Read `.ralph/kanban.md` and find the task entry for the given ID
- Extract Description, Scope, Acceptance Criteria, Dependencies
- Check dependent tasks to understand what they provide

**Ask initial clarifying questions:**
- What problem does this solve?
- What is the desired functionality?
- Are there any constraints or requirements not in the task?
- What does success look like?

**Output:** Clear understanding of requirements and constraints before diving into code.

---

### Phase 2: Codebase Exploration (Parallel Analysis)

**Goal:** Build comprehensive understanding of relevant existing code through parallel exploration of three dimensions.

**Dimension A - Similar Features:**
- Search for existing features that solve similar problems
- Trace execution paths from entry points through data transformations
- Document how existing features are structured

**Dimension B - Architecture & Patterns:**
- Map abstraction layers and module boundaries
- Identify design patterns used in the codebase
- Understand technology stack and conventions

**Dimension C - Integration Points:**
- Find code that will interact with the new feature
- Identify shared utilities, services, and data models
- Understand testing patterns and coverage expectations

**Exploration tools (READ-ONLY):**
- **Glob**: Find files by pattern
- **Grep**: Search for code patterns, function names, imports
- **Read**: Examine specific files in detail
- **Bash** (read-only): `ls`, `git log`, `git diff`

**Output:** Identify 5-10 key files for reference with specific insights from each.

---

### Phase 3: Clarifying Questions (CRITICAL)

**Goal:** Address all remaining ambiguities before designing architecture.

> ⚠️ **This is one of the most important phases. Do not skip it.**

**Consolidate questions from exploration into categories:**

1. **Edge Cases**: What happens when X fails? What if Y is empty?
2. **Error Handling**: How should errors be surfaced? Retry logic?
3. **Integration Points**: How should this interact with existing system X?
4. **Design Preferences**: Performance vs simplicity? Explicit vs convention?
5. **Scope Boundaries**: What's explicitly out of scope?

**AskUserQuestion Format:**
```
- question: Clear, specific question ending with ?
- header: Short label (max 12 chars)
- multiSelect: false (unless choices aren't mutually exclusive)
- options: 2-4 specific choices grounded in codebase findings
  - label: Concise choice text (1-5 words)
  - description: Context from exploration (file paths, patterns found)
```

**Guidelines:**
- Ground every option in codebase findings (cite file paths)
- One decision per question (avoid compound questions)
- Provide trade-off context in descriptions
- Ask 3-6 questions for complex features

**Output:** All ambiguities resolved with clear decisions documented.

---

### Phase 4: Architecture Design (Multiple Approaches)

**Goal:** Present 2-3 architecture approaches with trade-off analysis, then recommend the best fit.

**Generate approaches:**

| Approach | Description | When to Use |
|----------|-------------|-------------|
| **Minimal Changes** | Smallest possible footprint, follows existing patterns exactly | Time-critical, low-risk features |
| **Clean Architecture** | Ideal design with proper abstractions and separation | Foundational features, long-term maintainability |
| **Pragmatic Balance** | Balanced trade-off between minimal and clean | Most features; good default |

**For each approach, document:**
- Key architectural decisions and rationale
- Component design with file paths and responsibilities
- Data flow from entry points through transformations
- Files to CREATE vs MODIFY vs REFERENCE
- Pros and cons

**Present trade-off analysis:**
```
questions:
  - question: Which architecture approach should we use?
    header: Approach
    multiSelect: false
    options:
      - label: Minimal Changes (Recommended)
        description: "Add to existing X pattern in src/Y. Fast, low risk. Trade-off: less flexible"
      - label: Clean Architecture
        description: "New abstraction layer with proper interfaces. Trade-off: more files, higher effort"
      - label: Pragmatic Balance
        description: "Extend existing patterns with targeted improvements. Trade-off: moderate complexity"
```

**After user selection, confirm before proceeding:**
```
questions:
  - question: Ready to finalize the implementation plan with this approach?
    header: Confirm
    multiSelect: false
    options:
      - label: Yes, write the plan
        description: Finalize plan with selected architecture
      - label: Explore more
        description: I have more questions or want to reconsider
```

**Output:** Selected architecture approach with user approval.

---

### Phase 5: Write the Plan (REQUIRED)

**Goal:** Document the complete implementation plan.

**You MUST write the plan to `.ralph/plans/TASK-ID.md`** - this is not optional.

**Plan must include:**
- Selected architecture approach and rationale
- Patterns discovered during exploration (with file references)
- Step-by-step implementation sequence
- Critical files table (CREATE/MODIFY/REFERENCE)
- Potential challenges and mitigations
- Decisions made during clarifying questions

For plan structure and format, see references/plan-format.md.

---

### Phase 6: Summary

**Goal:** Document accomplishments and provide clear next steps.

**Present summary to user:**
- What was planned and why
- Key architectural decisions made
- Critical files identified
- Potential challenges flagged
- Suggested next steps (run worker, need more planning, etc.)

**Output:** User has clear understanding of the plan and confidence to proceed.

## Examples

### Example 1: Planning an Existing Task (Full 7-Phase Workflow)

**User**: `/wiggum-plan TASK-015`

---

**Phase 1: Discovery**

**Assistant**: I'll create an implementation plan for TASK-015 using the 7-phase workflow. Let me start with discovery.

*[Reads .ralph/kanban.md]*

Found TASK-015:
```
- [ ] **[TASK-015]** Create auth routes (login/register)
  - Description: Create POST /auth/login and POST /auth/register endpoints
  - Priority: HIGH
  - Dependencies: TASK-013, TASK-014, TASK-010
```

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: What is the primary goal for these auth routes?
    header: Goal
    multiSelect: false
    options:
      - label: User authentication
        description: Standard login/register for existing user base
      - label: OAuth integration
        description: Third-party auth (Google, GitHub, etc.)
      - label: API authentication
        description: Machine-to-machine API access tokens
```

**User selects**: User authentication

---

**Phase 2: Codebase Exploration**

**Assistant**: Now exploring the codebase across three dimensions...

**Dimension A - Similar Features:**
*[Uses Glob to find route files]*
*[Uses Read to examine src/routes/users.ts]*

Found route pattern using Express Router with controller separation:
- `src/routes/users.ts:15` - Route definition pattern
- `src/controllers/userController.ts` - Controller pattern with error handling

**Dimension B - Architecture & Patterns:**
*[Uses Grep to find validation patterns]*
*[Uses Read to examine src/middleware/]*

Found:
- Validation using `express-validator` in existing routes
- Error handling middleware at `src/middleware/errorHandler.ts`
- Request logging at `src/middleware/logger.ts`

**Dimension C - Integration Points:**
*[Uses Read to examine dependent tasks' outputs]*

Dependencies provide:
- TASK-013: JWT utilities at `src/utils/jwt.ts`
- TASK-014: Auth middleware at `src/middleware/auth.ts`
- TASK-010: API routing base at `src/routes/index.ts`

**Key files identified (8 total):**
| File | Insight |
|------|---------|
| `src/routes/users.ts` | Route pattern to follow |
| `src/controllers/userController.ts` | Controller structure |
| `src/middleware/auth.ts` | Auth middleware from TASK-014 |
| `src/utils/jwt.ts` | JWT utils from TASK-013 |
| `src/middleware/rate-limit.ts` | Existing rate limiter |
| `src/middleware/errorHandler.ts` | Error handling pattern |
| `src/models/User.ts` | User model structure |
| `src/validators/index.ts` | Validation patterns |

---

**Phase 3: Clarifying Questions**

**Assistant**: Based on exploration, I have clarifying questions across key decision areas.

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: Should registration require email verification?
    header: Email verify
    multiSelect: false
    options:
      - label: No verification (Recommended)
        description: User gets immediate access. Simpler, matches existing user flow
      - label: Email verification
        description: Requires email service integration (not currently in codebase)
  - question: What password requirements should we enforce?
    header: Password
    multiSelect: false
    options:
      - label: Minimum 8 chars
        description: Simple requirement, good UX, found in similar apps
      - label: Complex rules
        description: Upper, lower, number, special char - more secure but friction
  - question: Should failed logins be rate-limited?
    header: Rate limit
    multiSelect: false
    options:
      - label: Yes, use existing pattern (Recommended)
        description: Found rate-limiter at src/middleware/rate-limit.ts
      - label: No rate limiting
        description: Simpler but vulnerable to brute force
  - question: How should login errors be reported?
    header: Errors
    multiSelect: false
    options:
      - label: Generic message
        description: "Invalid credentials" - security best practice
      - label: Specific message
        description: "Wrong password" vs "User not found" - better UX, info leak risk
```

**User selects**: No verification, Minimum 8 chars, Yes use existing pattern, Generic message

**Assistant**: Decisions recorded. All ambiguities resolved.

---

**Phase 4: Architecture Design**

**Assistant**: I'll present three architecture approaches with trade-offs.

### Approach 1: Minimal Changes
- Add routes directly to existing `src/routes/index.ts`
- Inline validation logic
- Reuse existing patterns exactly
- **Pros**: Fast, low risk, familiar patterns
- **Cons**: Larger single file, less separation

### Approach 2: Clean Architecture
- New `src/routes/auth.ts` with dedicated router
- New `src/controllers/authController.ts` with separated concerns
- New `src/validators/auth.ts` for validation schemas
- New `src/services/authService.ts` for business logic
- **Pros**: Proper separation, testable, maintainable
- **Cons**: More files, higher initial effort

### Approach 3: Pragmatic Balance
- New `src/routes/auth.ts` with dedicated router
- New `src/controllers/authController.ts`
- Reuse existing validator patterns inline
- **Pros**: Good separation without over-engineering
- **Cons**: Validation not reusable

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: Which architecture approach should we use?
    header: Approach
    multiSelect: false
    options:
      - label: Pragmatic Balance (Recommended)
        description: New auth router + controller, inline validation. Good balance
      - label: Clean Architecture
        description: Full separation with service layer. Best for complex auth
      - label: Minimal Changes
        description: Add to existing routes. Fast but less organized
```

**User selects**: Pragmatic Balance

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: Ready to finalize the implementation plan with Pragmatic Balance approach?
    header: Confirm
    multiSelect: false
    options:
      - label: Yes, write the plan
        description: Finalize plan with selected architecture
      - label: Explore more
        description: I have more questions
```

**User selects**: Yes, write the plan

---

**Phase 5: Write the Plan**

**Assistant**: Writing the implementation plan...

*[Writes to .ralph/plans/TASK-015.md]*

Plan written with:
- Pragmatic Balance architecture
- Route at `src/routes/auth.ts`
- Controller at `src/controllers/authController.ts`
- Rate limiting on login endpoint
- Password validation (min 8 chars)
- Generic error messages

---

**Phase 6: Summary**

**Assistant**: ✓ Implementation plan complete for TASK-015.

**What was planned:**
- POST `/auth/login` and POST `/auth/register` endpoints
- Following Pragmatic Balance architecture

**Key decisions made:**
- No email verification (immediate access)
- 8-char minimum password
- Rate limiting on login (using existing middleware)
- Generic error messages for security

**Critical files:**
| File | Action |
|------|--------|
| `src/routes/auth.ts` | CREATE |
| `src/controllers/authController.ts` | CREATE |
| `src/routes/index.ts` | MODIFY (mount auth routes) |

**Next steps:**
- Run `wiggum run TASK-015` to execute with a worker
- Or review plan at `.ralph/plans/TASK-015.md` first

---

### Example 2: Creating Task and Plan Together

**User**: `/wiggum-plan Add a dark mode toggle to the settings page`

**Phase 0: Task Creation**

**Assistant**: Since no task ID was provided, I'll first create the task.

*[Reads .ralph/kanban.md]*

Found 15 tasks. Highest ID is TASK-015. TASK-012 (Settings page) is complete `[x]`.

*[Uses AskUserQuestion]*
```yaml
questions:
  - question: What priority level for dark mode?
    header: Priority
    multiSelect: false
    options:
      - label: MEDIUM (Recommended)
        description: Nice-to-have UX enhancement
      - label: HIGH
        description: Important, blocking other work
      - label: LOW
        description: Low priority
  - question: What should be included in dark mode scope?
    header: Scope
    multiSelect: true
    options:
      - label: Settings toggle
        description: UI toggle in settings page
      - label: System preference
        description: Auto-detect OS dark/light preference
      - label: Persist choice
        description: Remember selection across sessions
```

**User selects**: MEDIUM, Settings toggle, Persist choice

*[Creates TASK-016 in kanban, then proceeds through Phases 1-6]*

...

**Phase 6: Summary**

**Assistant**: ✓ Created TASK-016 and implementation plan.

**Task created:** TASK-016 - Add dark mode toggle to settings page (MEDIUM)

**Architecture:** CSS variables approach with body class toggle

**Key decisions:**
- Theme stored in localStorage
- No system preference detection (out of scope)
- Immediate toggle effect (no animation)

**Plan saved to:** `.ralph/plans/TASK-016.md`

## Key Principles

1. **Follow the 7 phases** - Discovery → Exploration → Questions → Architecture → Plan → Summary
2. **Parallel exploration** - Analyze similar features, architecture, and integration points together
3. **Questions are critical** - Phase 3 is one of the most important; never skip it
4. **Multiple approaches** - Present 2-3 architecture options with trade-off analysis
5. **Get approval** - Confirm architecture choice before writing plan
6. **Ground in findings** - Every option must reference actual codebase patterns
7. **Always write plan** - Session must end with `.ralph/plans/TASK-ID.md`
8. **Never implement** - Planning only, no code changes

## Progressive Disclosure

This SKILL.md contains the core workflow. For detailed guidance:
- **Plan format**: references/plan-format.md
- **Exploration strategies**: references/exploration-strategies.md
- **Question patterns**: references/question-patterns.md
