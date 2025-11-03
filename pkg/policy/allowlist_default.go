package policy

// DefaultAllowedDomains returns the default allowlist derived from Claude Code docs
// plus additional Sprite/Fly domains requested by the user.
// Source: https://docs.claude.com/en/docs/claude-code/claude-code-on-the-web#default-allowed-domains
func DefaultAllowedDomains() []string {
	return []string{
		// AI Services - Anthropic/Claude
		"api.anthropic.com",
		"statsig.anthropic.com",
		"claude.ai",
		
		// AI Services - OpenAI
		"api.openai.com",
		"platform.openai.com",
		"chat.openai.com",
		"openai.com",
		
		// AI Services - GitHub Copilot
		"copilot-proxy.githubusercontent.com",
		"api.githubcopilot.com",
		"copilot.github.com",
		
		// AI Services - Other
		"gemini.google.com",
		"generativelanguage.googleapis.com",
		"ai.google.dev",

		// Version Control
		"github.com", "www.github.com", "api.github.com",
		"raw.githubusercontent.com", "objects.githubusercontent.com", "codeload.github.com",
		"avatars.githubusercontent.com", "camo.githubusercontent.com", "gist.github.com",
		"gitlab.com", "www.gitlab.com", "registry.gitlab.com",
		"bitbucket.org", "www.bitbucket.org", "api.bitbucket.org",

		// Container Registries
		"registry-1.docker.io", "auth.docker.io", "index.docker.io",
		"hub.docker.com", "www.docker.com", "production.cloudflare.docker.com", "download.docker.com",
		"*.gcr.io", "ghcr.io", "mcr.microsoft.com", "*.data.mcr.microsoft.com",

		// Cloud Platforms (partial list, key endpoints)
		"cloud.google.com", "accounts.google.com", "gcloud.google.com", "*.googleapis.com",
		"storage.googleapis.com", "compute.googleapis.com", "container.googleapis.com",
		"azure.com", "portal.azure.com", "microsoft.com", "www.microsoft.com", "*.microsoftonline.com",
		"packages.microsoft.com", "dotnet.microsoft.com", "dot.net", "visualstudio.com", "dev.azure.com",
		"oracle.com", "www.oracle.com", "java.com", "www.java.com", "java.net", "www.java.net",
		"download.oracle.com", "yum.oracle.com",

		// JS/Node package managers
		"registry.npmjs.org", "www.npmjs.com", "www.npmjs.org", "npmjs.com", "npmjs.org",
		"yarnpkg.com", "registry.yarnpkg.com",

		// Python package managers
		"pypi.org", "www.pypi.org", "files.pythonhosted.org", "pythonhosted.org",
		"test.pypi.org", "pypi.python.org", "pypa.io", "www.pypa.io",

		// Rust
		"crates.io", "www.crates.io", "static.crates.io", "rustup.rs", "static.rust-lang.org", "www.rust-lang.org",

		// Go
		"proxy.golang.org", "sum.golang.org", "index.golang.org", "golang.org", "www.golang.org",
		"goproxy.io", "pkg.go.dev",

		// JVM
		"maven.org", "repo.maven.org", "central.maven.org", "repo1.maven.org",
		"jcenter.bintray.com", "gradle.org", "www.gradle.org", "services.gradle.org",
		"spring.io", "repo.spring.io",

		// Linux distros key
		"archive.ubuntu.com", "security.ubuntu.com", "ubuntu.com", "www.ubuntu.com", "*.ubuntu.com",
		"ppa.launchpad.net", "launchpad.net", "www.launchpad.net",

		// Dev tools
		"dl.k8s.io", "pkgs.k8s.io", "k8s.io", "www.k8s.io",
		"releases.hashicorp.com", "apt.releases.hashicorp.com", "rpm.releases.hashicorp.com", "archive.releases.hashicorp.com",
		"hashicorp.com", "www.hashicorp.com",
		"nodejs.org", "www.nodejs.org",

		// Cloud services & monitoring
		"statsig.com", "www.statsig.com", "api.statsig.com", "*.sentry.io",

		// Content delivery & mirrors
		"*.sourceforge.net", "packagecloud.io", "*.packagecloud.io",

		// Schema & configuration
		"json-schema.org", "www.json-schema.org", "json.schemastore.org", "www.schemastore.org",

		// Sprite/Fly additions
		"api.fly.io", "api.machines.dev", "api.sprites.dev", "sprites.dev", "fly.io",
	}
}
