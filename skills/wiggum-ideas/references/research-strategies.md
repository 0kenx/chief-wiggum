# Research Strategies Reference

## Codebase Analysis

Explore the codebase at a high level to understand:

### What to Look For

**Technical Debt:**
- TODO/FIXME comments indicating deferred work
- Deprecated patterns still in use
- Inconsistent error handling across modules

**Security Concerns:**
- Authentication and authorization gaps
- Input validation inconsistencies
- Exposed sensitive data in logs or responses

**Performance Opportunities:**
- Database query patterns that could be optimized
- Missing caching layers
- Synchronous operations that could be async

**Reliability Gaps:**
- Missing retry logic for external services
- Incomplete error handling
- Lack of circuit breakers

**Architectural Issues:**
- Inconsistent patterns across modules
- Missing abstractions
- Tight coupling between components

## Market Research

**Use the WebSearch tool** for all market research.

### Research Areas

**Industry Best Practices:**
- Current standards for the product category
- Emerging patterns and approaches
- Compliance requirements (SOC2, GDPR, etc.)

**Competitive Landscape:**
- Features competitors offer
- Gaps in competitor offerings
- Differentiation opportunities

**User Expectations:**
- What users expect from this type of product
- Common pain points in the industry
- Feature requests and trends

**Technology Trends:**
- Emerging technologies that could provide advantages
- Frameworks and tools gaining adoption
- Patterns becoming industry standard

## Combining Findings

### Gap Analysis
1. List what the project currently has
2. List what research indicates it should have
3. The gaps become task candidates

### Opportunity Mapping
1. Identify findings from codebase analysis
2. Cross-reference with market research
3. Prioritize where codebase gaps align with market expectations

## Output Target

Each research session should generate enough findings to produce **30-50 tasks**:
- Continue exploring until you have substantial findings
- Cover multiple areas (security, performance, features, etc.)
- Include findings that could lead to innovative tasks
