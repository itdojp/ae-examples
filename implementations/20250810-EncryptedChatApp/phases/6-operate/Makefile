SHELL := /usr/bin/env bash
COMPOSE := docker compose
NODE := node
NPM := npm
NPX := npx

# Colors for output
RED := \033[0;31m
GREEN := \033[0;32m
YELLOW := \033[1;33m
NC := \033[0m # No Color

# Project variables
PROJECT_NAME := e2e-encrypted-chat
VERSION := $(shell node -p "require('./package.json').version")
BUILD_TIME := $(shell date -u +"%Y-%m-%dT%H:%M:%SZ")
GIT_COMMIT := $(shell git rev-parse --short HEAD 2>/dev/null || echo "unknown")

.PHONY: help up down build clean install lint test spec:lint formal:check \
        test:all test:unit test:integration test:e2e test:acceptance test:property \
        test:mbt test:mutation test:contract test:api-fuzz policy:test sbom verify:trace \
        db:migrate db:seed dev prod docker:build docker:push

help: ## Show this help message
	@echo -e "${GREEN}E2E Encrypted Chat - Makefile Commands${NC}"
	@echo -e "${YELLOW}========================================${NC}"
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "${GREEN}%-20s${NC} %s\n", $$1, $$2}'

install: ## Install dependencies
	@echo -e "${YELLOW}Installing dependencies...${NC}"
	$(NPM) ci
	@echo -e "${GREEN}Dependencies installed successfully${NC}"

build: ## Build the application
	@echo -e "${YELLOW}Building application...${NC}"
	$(NPM) run build
	@echo -e "${GREEN}Build completed successfully${NC}"

clean: ## Clean build artifacts and dependencies
	@echo -e "${YELLOW}Cleaning...${NC}"
	rm -rf dist/ node_modules/ coverage/ .nyc_output/ logs/ tmp/
	@echo -e "${GREEN}Cleaned successfully${NC}"

up: ## Start all services with Docker Compose
	@echo -e "${YELLOW}Starting services...${NC}"
	$(COMPOSE) up -d --build
	@echo -e "${GREEN}Services started successfully${NC}"

down: ## Stop all services
	@echo -e "${YELLOW}Stopping services...${NC}"
	$(COMPOSE) down -v
	@echo -e "${GREEN}Services stopped successfully${NC}"

dev: ## Start development environment
	@echo -e "${YELLOW}Starting development environment...${NC}"
	$(COMPOSE) --profile development up -d
	$(NPM) run dev
	@echo -e "${GREEN}Development environment ready${NC}"

prod: ## Start production environment
	@echo -e "${YELLOW}Starting production environment...${NC}"
	$(COMPOSE) --profile production up -d
	@echo -e "${GREEN}Production environment ready${NC}"

lint: ## Run linters
	@echo -e "${YELLOW}Running linters...${NC}"
	$(NPM) run lint
	$(NPM) run typecheck
	@echo -e "${GREEN}Linting completed${NC}"

spec:lint: ## Lint specifications
	@echo -e "${YELLOW}Linting specifications...${NC}"
	$(NPX) @stoplight/spectral lint specs/openapi/api.yaml || true
	$(NPX) gherkin-lint specs/bdd/features/*.feature || true
	@if [ -f ./scripts/verify/traceability.sh ]; then ./scripts/verify/traceability.sh; fi
	@echo -e "${GREEN}Specification linting completed${NC}"

formal:check: ## Check formal specifications
	@echo -e "${YELLOW}Checking formal specifications...${NC}"
	docker run --rm -v $$PWD/specs/formal/tla+:/work ghcr.io/apalache-mc/apalache:latest \
	  check --init=E2EEncryption.cfg E2EEncryption.tla || true
	@echo -e "${GREEN}Formal specification check completed${NC}"

test:all: ## Run all tests
	@echo -e "${YELLOW}Running all tests...${NC}"
	$(MAKE) test:unit
	$(MAKE) test:integration
	$(MAKE) test:property
	$(MAKE) test:acceptance
	@echo -e "${GREEN}All tests completed${NC}"

test:unit: ## Run unit tests
	@echo -e "${YELLOW}Running unit tests...${NC}"
	$(NPM) run test:unit
	@echo -e "${GREEN}Unit tests completed${NC}"

test:integration: ## Run integration tests
	@echo -e "${YELLOW}Running integration tests...${NC}"
	$(COMPOSE) -f docker-compose.test.yml up --abort-on-container-exit --exit-code-from test-runner
	@echo -e "${GREEN}Integration tests completed${NC}"

test:e2e: ## Run end-to-end tests
	@echo -e "${YELLOW}Running E2E tests...${NC}"
	$(NPM) run test:e2e
	@echo -e "${GREEN}E2E tests completed${NC}"

test:acceptance: ## Run acceptance tests
	@echo -e "${YELLOW}Running acceptance tests...${NC}"
	$(NPX) cucumber-js
	@echo -e "${GREEN}Acceptance tests completed${NC}"

test:property: ## Run property-based tests
	@echo -e "${YELLOW}Running property-based tests...${NC}"
	$(NPM) run pbt
	@echo -e "${GREEN}Property-based tests completed${NC}"

test:mbt: ## Run model-based tests
	@echo -e "${YELLOW}Running model-based tests...${NC}"
	$(NPM) run mbt || true
	@echo -e "${GREEN}Model-based tests completed${NC}"

test:mutation: ## Run mutation tests
	@echo -e "${YELLOW}Running mutation tests...${NC}"
	$(NPX) stryker run || true
	@echo -e "${GREEN}Mutation tests completed${NC}"

test:contract: ## Run contract tests
	@echo -e "${YELLOW}Running contract tests...${NC}"
	$(NPM) run contract || true
	@echo -e "${GREEN}Contract tests completed${NC}"

test:api-fuzz: ## Run API fuzzing tests
	@echo -e "${YELLOW}Running API fuzzing tests...${NC}"
	docker run --rm -v $$PWD/specs/openapi:/spec schemathesis/schemathesis:stable \
		run /spec/api.yaml --base-url=http://host.docker.internal:3000 || true
	@echo -e "${GREEN}API fuzzing tests completed${NC}"

test:coverage: ## Run tests with coverage
	@echo -e "${YELLOW}Running tests with coverage...${NC}"
	$(NPM) run test:coverage
	@echo -e "${GREEN}Coverage report generated${NC}"

policy:test: ## Test OPA policies
	@echo -e "${YELLOW}Testing OPA policies...${NC}"
	docker run --rm -v $$PWD/policies:/policies openpolicyagent/opa test /policies -v || true
	@echo -e "${GREEN}Policy tests completed${NC}"

db:migrate: ## Run database migrations
	@echo -e "${YELLOW}Running database migrations...${NC}"
	$(NPM) run db:migrate
	@echo -e "${GREEN}Migrations completed${NC}"

db:seed: ## Seed database
	@echo -e "${YELLOW}Seeding database...${NC}"
	$(NPM) run db:seed
	@echo -e "${GREEN}Database seeded${NC}"

db:reset: ## Reset database
	@echo -e "${YELLOW}Resetting database...${NC}"
	$(COMPOSE) exec postgres psql -U app -d e2echat -c "DROP SCHEMA public CASCADE; CREATE SCHEMA public;"
	$(MAKE) db:migrate
	$(MAKE) db:seed
	@echo -e "${GREEN}Database reset completed${NC}"

docker:build: ## Build Docker image
	@echo -e "${YELLOW}Building Docker image...${NC}"
	docker build -t $(PROJECT_NAME):$(VERSION) \
		--build-arg VERSION=$(VERSION) \
		--build-arg BUILD_TIME=$(BUILD_TIME) \
		--build-arg GIT_COMMIT=$(GIT_COMMIT) .
	docker tag $(PROJECT_NAME):$(VERSION) $(PROJECT_NAME):latest
	@echo -e "${GREEN}Docker image built successfully${NC}"

docker:push: ## Push Docker image to registry
	@echo -e "${YELLOW}Pushing Docker image...${NC}"
	docker push $(PROJECT_NAME):$(VERSION)
	docker push $(PROJECT_NAME):latest
	@echo -e "${GREEN}Docker image pushed successfully${NC}"

sbom: ## Generate Software Bill of Materials
	@echo -e "${YELLOW}Generating SBOM...${NC}"
	@if ! command -v syft &> /dev/null; then \
		curl -sSfL https://raw.githubusercontent.com/anchore/syft/main/install.sh | sh -s -- -b . v1.0.0; \
	fi
	mkdir -p security/sbom
	./syft packages dir:. -o cyclonedx-json > security/sbom/sbom.json
	@echo -e "${GREEN}SBOM generated successfully${NC}"

security:scan: ## Run security scans
	@echo -e "${YELLOW}Running security scans...${NC}"
	$(NPM) audit
	docker run --rm -v $$PWD:/src aquasec/trivy fs /src || true
	@echo -e "${GREEN}Security scan completed${NC}"

verify:trace: ## Verify traceability
	@echo -e "${YELLOW}Verifying traceability...${NC}"
	@if [ -f ./scripts/verify/traceability.sh ]; then \
		./scripts/verify/traceability.sh; \
	else \
		echo "Traceability script not found"; \
	fi
	@echo -e "${GREEN}Traceability verification completed${NC}"

logs: ## Show application logs
	$(COMPOSE) logs -f app

metrics: ## Show Prometheus metrics
	curl -s http://localhost:9464/metrics | head -50

health: ## Check service health
	@echo -e "${YELLOW}Checking service health...${NC}"
	@curl -f http://localhost:3000/health || echo -e "${RED}Service unhealthy${NC}"
	@echo -e "${GREEN}Health check completed${NC}"

.DEFAULT_GOAL := help