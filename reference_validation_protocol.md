# Reference Validation Protocol

**Purpose**: Schema for systematic verification of bibliographic citations with full audit trail

**Version**: 0.1.0

**Related**: See [LRT_DEVELOPMENT_PROCESS.md](LRT_DEVELOPMENT_PROCESS.md) Phase 2 (Citation discipline) and Phase 6 (SME Pre-Review)

---

## Schema Definition

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "Citation Validation Record",
  "version": "0.1.0",
  "description": "Schema for systematic verification of bibliographic citations with full audit trail",

  "type": "object",
  "required": ["validation_metadata", "citation_input", "verification_result"],

  "properties": {

    "validation_metadata": {
      "type": "object",
      "description": "Provenance and context for the validation process",
      "required": ["validation_id", "timestamp", "validator", "protocol_version"],
      "properties": {
        "validation_id": {
          "type": "string",
          "format": "uuid",
          "description": "Unique identifier for this validation record"
        },
        "timestamp": {
          "type": "string",
          "format": "date-time",
          "description": "ISO 8601 timestamp of validation"
        },
        "validator": {
          "type": "object",
          "properties": {
            "type": {
              "type": "string",
              "enum": ["human", "ai", "hybrid", "automated_tool"]
            },
            "identifier": {
              "type": "string",
              "description": "Model name, ORCID, or tool identifier"
            },
            "version": {
              "type": "string"
            }
          }
        },
        "protocol_version": {
          "type": "string",
          "description": "Version of validation protocol applied"
        },
        "context": {
          "type": "object",
          "properties": {
            "source_document": {
              "type": "string",
              "description": "Document from which citation was extracted"
            },
            "requesting_party": {
              "type": "string"
            },
            "validation_purpose": {
              "type": "string",
              "enum": ["pre_publication", "literature_review", "fact_check", "systematic_review", "other"]
            }
          }
        }
      }
    },

    "citation_input": {
      "type": "object",
      "description": "The citation as originally provided",
      "required": ["raw_text", "input_format"],
      "properties": {
        "raw_text": {
          "type": "string",
          "description": "Verbatim citation as received"
        },
        "input_format": {
          "type": "string",
          "enum": ["bibtex", "ris", "plain_text", "structured_json", "apa", "mla", "chicago", "harvard", "ieee", "unknown"]
        },
        "parsed_fields": {
          "type": "object",
          "description": "Citation decomposed into fields",
          "properties": {
            "authors": {
              "type": "array",
              "items": {
                "type": "object",
                "properties": {
                  "family_name": {"type": "string"},
                  "given_name": {"type": "string"},
                  "orcid": {"type": "string"},
                  "position": {"type": "integer"}
                }
              }
            },
            "title": {"type": "string"},
            "year": {"type": "integer"},
            "venue": {
              "type": "object",
              "properties": {
                "type": {
                  "type": "string",
                  "enum": ["journal", "conference", "book", "chapter", "thesis", "report", "preprint", "website", "other"]
                },
                "name": {"type": "string"},
                "publisher": {"type": "string"},
                "volume": {"type": "string"},
                "issue": {"type": "string"},
                "pages": {"type": "string"},
                "editors": {
                  "type": "array",
                  "items": {"type": "string"}
                }
              }
            },
            "identifiers": {
              "type": "object",
              "properties": {
                "doi": {"type": "string"},
                "arxiv": {"type": "string"},
                "pmid": {"type": "string"},
                "isbn": {"type": "string"},
                "url": {"type": "string", "format": "uri"}
              }
            }
          }
        }
      }
    },

    "verification_result": {
      "type": "object",
      "required": ["overall_status", "field_verification", "sources_consulted"],
      "properties": {

        "overall_status": {
          "type": "string",
          "enum": ["VERIFIED", "VERIFIED_WITH_CORRECTIONS", "PARTIALLY_VERIFIED", "UNVERIFIED", "REFUTED", "NONEXISTENT"],
          "description": "VERIFIED: All fields confirmed. VERIFIED_WITH_CORRECTIONS: Exists but input had errors. PARTIALLY_VERIFIED: Some fields confirmed, others unverifiable. UNVERIFIED: Could not confirm existence. REFUTED: Confirmed to be erroneous. NONEXISTENT: Source does not exist."
        },

        "confidence": {
          "type": "string",
          "enum": ["HIGH", "MEDIUM", "LOW"],
          "description": "HIGH: Multiple authoritative sources agree. MEDIUM: Single authoritative source or multiple secondary. LOW: Only indirect evidence."
        },

        "field_verification": {
          "type": "object",
          "description": "Per-field verification status",
          "properties": {
            "authors": {
              "$ref": "#/definitions/field_status"
            },
            "title": {
              "$ref": "#/definitions/field_status"
            },
            "year": {
              "$ref": "#/definitions/field_status"
            },
            "venue": {
              "$ref": "#/definitions/field_status"
            },
            "volume_issue_pages": {
              "$ref": "#/definitions/field_status"
            },
            "identifiers": {
              "$ref": "#/definitions/field_status"
            }
          }
        },

        "errors_found": {
          "type": "array",
          "items": {
            "type": "object",
            "required": ["field", "error_type", "provided_value"],
            "properties": {
              "field": {
                "type": "string"
              },
              "error_type": {
                "type": "string",
                "enum": [
                  "WRONG_JOURNAL",
                  "WRONG_YEAR",
                  "WRONG_VOLUME_ISSUE",
                  "WRONG_PAGES",
                  "WRONG_AUTHORS",
                  "WRONG_TITLE",
                  "WRONG_PUBLISHER",
                  "WRONG_EDITOR",
                  "CONFLATED_SOURCES",
                  "CRAWLER_ARTIFACT",
                  "HALLUCINATED",
                  "PREPRINT_NOT_PUBLISHED",
                  "PUBLISHED_NOT_PREPRINT",
                  "PARTIAL_MATCH",
                  "OTHER"
                ]
              },
              "provided_value": {
                "type": "string"
              },
              "correct_value": {
                "type": "string"
              },
              "explanation": {
                "type": "string"
              }
            }
          }
        },

        "sources_consulted": {
          "type": "array",
          "description": "Audit trail of verification sources",
          "items": {
            "type": "object",
            "required": ["source_type", "source_url", "consulted_at", "result"],
            "properties": {
              "source_type": {
                "type": "string",
                "enum": [
                  "publisher_page",
                  "doi_resolution",
                  "arxiv",
                  "pubmed",
                  "google_scholar",
                  "semantic_scholar",
                  "crossref",
                  "author_institutional_page",
                  "author_orcid",
                  "author_cv",
                  "library_catalog",
                  "philpapers",
                  "web_search",
                  "other"
                ]
              },
              "source_url": {
                "type": "string",
                "format": "uri"
              },
              "consulted_at": {
                "type": "string",
                "format": "date-time"
              },
              "result": {
                "type": "string",
                "enum": ["CONFIRMS", "CONTRADICTS", "PARTIAL", "NOT_FOUND", "INCONCLUSIVE"]
              },
              "fields_confirmed": {
                "type": "array",
                "items": {"type": "string"}
              },
              "fields_contradicted": {
                "type": "array",
                "items": {"type": "string"}
              },
              "notes": {
                "type": "string"
              }
            }
          }
        },

        "corrected_citation": {
          "type": "object",
          "description": "Corrected citation if errors were found",
          "properties": {
            "formatted_text": {
              "type": "string",
              "description": "Corrected citation in standard format"
            },
            "bibtex": {
              "type": "string"
            },
            "fields": {
              "$ref": "#/properties/citation_input/properties/parsed_fields"
            }
          }
        }
      }
    },

    "verification_notes": {
      "type": "object",
      "properties": {
        "process_notes": {
          "type": "string",
          "description": "Free-text notes on verification process"
        },
        "anomalies": {
          "type": "array",
          "items": {"type": "string"},
          "description": "Unusual findings worth noting"
        },
        "recommendations": {
          "type": "array",
          "items": {"type": "string"},
          "description": "Suggested follow-up actions"
        },
        "time_spent_seconds": {
          "type": "integer"
        }
      }
    }
  },

  "definitions": {
    "field_status": {
      "type": "object",
      "required": ["status"],
      "properties": {
        "status": {
          "type": "string",
          "enum": ["CONFIRMED", "CORRECTED", "UNVERIFIED", "CONTRADICTED", "NOT_APPLICABLE"]
        },
        "source": {
          "type": "string",
          "description": "Which source confirmed/contradicted this field"
        },
        "notes": {
          "type": "string"
        }
      }
    }
  }
}
```

---

## Status Codes

### Overall Status

| Status | Meaning |
|--------|---------|
| `VERIFIED` | All fields confirmed against authoritative sources |
| `VERIFIED_WITH_CORRECTIONS` | Source exists but input had errors (corrections provided) |
| `PARTIALLY_VERIFIED` | Some fields confirmed, others unverifiable |
| `UNVERIFIED` | Could not confirm existence through available sources |
| `REFUTED` | Confirmed to be erroneous (wrong attribution, etc.) |
| `NONEXISTENT` | Source does not exist (hallucinated or fabricated) |

### Confidence Levels

| Level | Meaning |
|-------|---------|
| `HIGH` | Multiple authoritative sources agree |
| `MEDIUM` | Single authoritative source or multiple secondary sources |
| `LOW` | Only indirect evidence available |

### Error Types

| Error Type | Description |
|------------|-------------|
| `HALLUCINATED` | Citation appears to be fabricated (no evidence source exists) |
| `CONFLATED_SOURCES` | Multiple real sources merged into one false citation |
| `CRAWLER_ARTIFACT` | Error from web scraping (mangled text, wrong metadata) |
| `WRONG_JOURNAL` | Paper exists but in different venue |
| `WRONG_YEAR` | Paper exists but published different year |
| `WRONG_AUTHORS` | Author list incorrect |
| `PREPRINT_NOT_PUBLISHED` | Cited as published but only exists as preprint |
| `PUBLISHED_NOT_PREPRINT` | Cited as preprint but has been published |

---

## Usage in LRT Development

This protocol supports the citation discipline requirements in [LRT_DEVELOPMENT_PROCESS.md](LRT_DEVELOPMENT_PROCESS.md):

1. **Phase 2 (Multi-LLM Adversarial Review)**: AI systems flag citations for verification
2. **Phase 3 (Human Review)**: Human verifies flagged citations using this schema
3. **Phase 6 (SME Pre-Review)**: Community can request citation verification records

### Integration with Development Process

When a citation is flagged:
1. Create validation record with `validation_metadata`
2. Document original citation in `citation_input`
3. Consult sources and record in `sources_consulted`
4. Determine `overall_status` and `confidence`
5. If errors found, provide `corrected_citation`
6. Store record for audit trail

---

## Document History

| Date | Change | Version |
|------|--------|---------|
| 2025-11-29 | Created | 0.1.0 |
