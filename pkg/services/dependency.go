package services

import (
	"fmt"
)

// validateDependencies checks for circular dependencies and missing services
func (m *Manager) validateDependencies(svc *Service) error {
	// Check for self-dependency
	for _, need := range svc.Needs {
		if need == svc.Name {
			return fmt.Errorf("service cannot depend on itself")
		}
	}

	// Get all services
	services, err := m.db.ListServices()
	if err != nil {
		return fmt.Errorf("failed to load services: %w", err)
	}

	// Build service map including the new service
	svcMap := make(map[string]*Service)
	for _, s := range services {
		svcMap[s.Name] = s
	}
	// Add the new service to the map for cycle detection
	svcMap[svc.Name] = svc

	// Check if all dependencies exist (except for the service being created)
	for _, need := range svc.Needs {
		if _, exists := svcMap[need]; !exists {
			return fmt.Errorf("dependency not found: %s", need)
		}
	}

	// Check for circular dependencies using DFS
	visited := make(map[string]bool)
	recStack := make(map[string]bool)
	
	var hasCycle func(name string) bool
	hasCycle = func(name string) bool {
		visited[name] = true
		recStack[name] = true

		if s, exists := svcMap[name]; exists && s != nil {
			for _, dep := range s.Needs {
				if !visited[dep] {
					if hasCycle(dep) {
						return true
					}
				} else if recStack[dep] {
					return true
				}
			}
		}

		recStack[name] = false
		return false
	}

	// Start DFS from the new service
	if hasCycle(svc.Name) {
		return fmt.Errorf("circular dependency detected")
	}

	return nil
}

// calculateStartOrder calculates the order for starting services
// Services are returned in dependency order (dependencies before dependents)
func calculateStartOrder(deps map[string][]string) ([]string, error) {
	// Validate dependencies first
	if err := validateNoCycles(deps); err != nil {
		return nil, err
	}

	// Calculate topological order (dependencies first)
	var order []string
	visited := make(map[string]bool)
	temp := make(map[string]bool)

	var visit func(string) error
	visit = func(service string) error {
		if temp[service] {
			return fmt.Errorf("circular dependency detected involving %s", service)
		}
		if visited[service] {
			return nil
		}

		temp[service] = true
		
		// Visit dependencies first
		if dependencies, exists := deps[service]; exists {
			for _, dep := range dependencies {
				if err := visit(dep); err != nil {
					return err
				}
			}
		}
		
		temp[service] = false
		visited[service] = true
		order = append(order, service)
		return nil
	}

	// Visit all services
	for service := range deps {
		if err := visit(service); err != nil {
			return nil, err
		}
	}

	return order, nil
}

// validateNoCycles checks if the dependency graph has any cycles
func validateNoCycles(deps map[string][]string) error {
	visited := make(map[string]bool)
	recStack := make(map[string]bool)

	var hasCycle func(string) bool
	hasCycle = func(node string) bool {
		visited[node] = true
		recStack[node] = true

		for _, dep := range deps[node] {
			if !visited[dep] {
				if hasCycle(dep) {
					return true
				}
			} else if recStack[dep] {
				return true
			}
		}

		recStack[node] = false
		return false
	}

	// Check from each unvisited node
	for node := range deps {
		if !visited[node] {
			if hasCycle(node) {
				return fmt.Errorf("circular dependency detected")
			}
		}
	}

	return nil
}

// calculateShutdownOrder returns services in order they should be shut down
func (m *Manager) calculateShutdownOrder(services []*Service, dependents map[string][]string) []string {
	visited := make(map[string]bool)
	order := []string{}

	var visit func(name string)
	visit = func(name string) {
		if visited[name] {
			return
		}
		visited[name] = true

		// Visit all services that depend on this one first
		for _, dependent := range dependents[name] {
			visit(dependent)
		}

		order = append(order, name)
	}

	// Visit all services
	for _, svc := range services {
		visit(svc.Name)
	}

	return order
}

// groupByDependencyLevel groups services by their dependency level
func (m *Manager) groupByDependencyLevel(order []string, services []*Service) [][]string {
	// Build service map
	svcMap := make(map[string]*Service)
	for _, svc := range services {
		svcMap[svc.Name] = svc
	}

	// Calculate levels
	levels := make(map[string]int)
	var calcLevel func(name string) int
	calcLevel = func(name string) int {
		if level, exists := levels[name]; exists {
			return level
		}

		svc, exists := svcMap[name]
		if !exists {
			return 0
		}

		maxDepLevel := -1
		for _, dep := range svc.Needs {
			depLevel := calcLevel(dep)
			if depLevel > maxDepLevel {
				maxDepLevel = depLevel
			}
		}

		levels[name] = maxDepLevel + 1
		return maxDepLevel + 1
	}

	// Calculate level for all services
	maxLevel := -1
	for _, name := range order {
		level := calcLevel(name)
		if level > maxLevel {
			maxLevel = level
		}
	}

	// Group by level
	result := make([][]string, maxLevel+1)
	for name, level := range levels {
		result[level] = append(result[level], name)
	}

	return result
}
