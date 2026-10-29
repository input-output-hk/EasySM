import SwiftUI
import UniformTypeIdentifiers

// MARK: - JSON loading helpers

/// Load and decode a JSON file from a URL.
func loadJSON<T: Decodable>(_ url: URL, as type: T.Type) throws -> T {
  let data = try Data(contentsOf: url)
  return try JSONDecoder().decode(T.self, from: data)
}

// MARK: - Demo window

struct ContentView: View {
  @State private var runID = 0
  @State private var configuration: AutomatonConfiguration?
  @State private var plan: AnimationPlan?
  @State private var loadError: Error?

  // Selected file URLs — default to the bundled example files.
  @State private var configURL: URL?
  @State private var planURL: URL?

  @State private var showConfigImporter = false
  @State private var showPlanImporter = false

  private var configFilename: String {
    configURL?.lastPathComponent ?? "multisig-config.json"
  }

  private var planFilename: String {
    planURL?.lastPathComponent ?? "multisig-plan.json"
  }

  var body: some View {
    Group {
      if let configuration, let plan {
        VStack(spacing: 12) {
          VStack(spacing: 2) {
            Text("EasySM Animation Engine")
              .font(.title2.bold())
            Text(configuration.contractName)
              .foregroundStyle(.secondary)
          }
          .padding(.top, 16)

          AutomatonAnimator(configuration: configuration, plan: plan, runID: runID)
            .id("\(configURL?.path ?? "")-\(planURL?.path ?? "")")
            .frame(maxWidth: .infinity, maxHeight: .infinity)

          Button("Start") { runID += 1 }
            .padding(.bottom, 16)
        }
        .frame(minWidth: 800, minHeight: 620)
      } else {
        VStack(spacing: 12) {
          Text("Loading…")
            .font(.title2)
          if let error = loadError {
            Text(error.localizedDescription)
              .foregroundStyle(.red)
              .font(.caption)
          }
        }
        .frame(minWidth: 800, minHeight: 620)
      }
    }
    .overlay(alignment: .topLeading) {
      Grid(alignment: .leading, horizontalSpacing: 6, verticalSpacing: 6) {
        GridRow {
          Button("Select Configuration") { showConfigImporter = true }
          Text(configFilename)
            .font(.caption)
            .foregroundStyle(.secondary)
            .help(configURL?.path ?? "")
        }
        GridRow {
          Button("Select Plan") { showPlanImporter = true }
          Text(planFilename)
            .font(.caption)
            .foregroundStyle(.secondary)
            .help(planURL?.path ?? "")
        }
      }
      .padding(8)
    }
    .fileImporter(isPresented: $showConfigImporter, allowedContentTypes: [.json]) { result in
      if case .success(let url) = result {
        if url.startAccessingSecurityScopedResource() {
          defer { url.stopAccessingSecurityScopedResource() }
          configURL = url
          loadConfiguration()
        }
      }
    }
    .fileImporter(isPresented: $showPlanImporter, allowedContentTypes: [.json]) { result in
      if case .success(let url) = result {
        if url.startAccessingSecurityScopedResource() {
          defer { url.stopAccessingSecurityScopedResource() }
          planURL = url
          loadPlan()
        }
      }
    }
    .task {
      configURL = Bundle.main.url(forResource: "multisig-config", withExtension: "json")
      planURL = Bundle.main.url(forResource: "multisig-plan", withExtension: "json")
      loadConfiguration()
      loadPlan()
    }
  }

  // MARK: - Loading

  private func loadConfiguration() {
    guard let url = configURL else { return }
    do {
      configuration = try loadJSON(url, as: AutomatonConfiguration.self)
      loadError = nil
    } catch {
      loadError = error
    }
  }

  private func loadPlan() {
    guard let url = planURL else { return }
    do {
      plan = try loadJSON(url, as: AnimationPlan.self)
      loadError = nil
    } catch {
      loadError = error
    }
  }
}
