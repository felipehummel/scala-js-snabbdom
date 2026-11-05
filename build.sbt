ThisBuild / tlBaseVersion := "0.3"

ThisBuild / scalaVersion := "3.1.2"
ThisBuild / organization := "io.github.felipehummel"
ThisBuild / organizationName := "felipehummel"
ThisBuild / startYear := Some(2022)
ThisBuild / homepage := Some(
  url("https://github.com/felipehummel/scala-js-snabbdom")
)
ThisBuild / scmInfo := Some(
  ScmInfo(
    url("https://github.com/felipehummel/scala-js-snabbdom"),
    "scm:git@github.com:felipehummel/scala-js-snabbdom.git"
  )
)
ThisBuild / tlSonatypeUseLegacyHost := false
// The fork has no Sonatype or PGP secrets, so CI publishes only from tags.
ThisBuild / tlCiReleaseBranches := Seq.empty

ThisBuild / developers := List(
  tlGitHubDev("buntec", "Christoph Bunte"),
  tlGitHubDev("felipehummel", "Felipe Hummel"),
  tlGitHubDev("armanbilge", "Arman Bilge"),
  tlGitHubDev("davesmith00000", "Dave Smith")
)

ThisBuild / githubWorkflowBuildMatrixAdditions +=
  "browser" -> List("Chrome", "Firefox")
ThisBuild / githubWorkflowBuildSbtStepPreamble += s"set Global / useJSEnv := JSEnv.$${{ matrix.browser }}"

ThisBuild / githubWorkflowBuild +=
  WorkflowStep.Sbt(
    List("bundleMon"),
    name = Some("Monitor artifact size"),
    // The BundleMon GitHub App is installed only on the upstream repository.
    cond = Some(
      "matrix.project == 'rootJS' && matrix.browser == 'Chrome' && github.event.repository.fork == false"
    )
  )

// The Lean build and the conformance run do not vary across the OS, Scala and
// Java matrix, so the job runs once.
ThisBuild / githubWorkflowAddedJobs += {
  val leanInputs =
    "hashFiles('formal/lean-toolchain', 'formal/lake-manifest.json', 'formal/lakefile.toml')"
  WorkflowJob(
    id = "formal",
    name = "Formal",
    oses = githubWorkflowOSes.value.toList.take(1),
    scalas = githubWorkflowScalaVersions.value.toList.take(1),
    javas = githubWorkflowJavaVersions.value.toList.take(1),
    timeoutMinutes = Some(60),
    steps = githubWorkflowJobSetup.value.toList ++ List(
      // A pinned release checked by digest: elan-init.sh would install
      // whichever elan release is latest at run time.
      WorkflowStep.Run(
        List(
          "curl -sSfL -o elan.tar.gz https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz",
          "echo '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  elan.tar.gz' | sha256sum -c",
          "tar xzf elan.tar.gz",
          "./elan-init -y --default-toolchain none"
        ),
        name = Some("Install elan"),
        workingDirectory = Some("${{ runner.temp }}")
      ),
      WorkflowStep.Run(
        List("echo \"$HOME/.elan/bin\" >> \"$GITHUB_PATH\""),
        name = Some("Add elan to PATH")
      ),
      WorkflowStep.Use(
        UseRef.Public("actions", "cache", "v4"),
        name = Some("Cache Lean build"),
        params = Map(
          "path" -> "formal/.lake",
          "key" -> s"lake-$${{ runner.os }}-$${{ $leanInputs }}-$${{ hashFiles('formal/**/*.lean') }}",
          "restore-keys" -> s"lake-$${{ runner.os }}-$${{ $leanInputs }}-"
        )
      ),
      WorkflowStep.Run(
        List("lake build"),
        name = Some("Check proofs"),
        workingDirectory = Some("formal")
      ),
      WorkflowStep.Run(
        List("formal/conformance.sh"),
        name = Some("Check Lean-Scala conformance")
      )
    )
  )
}

lazy val useJSEnv = settingKey[JSEnv]("Browser for running Scala.js tests")
Global / useJSEnv := JSEnv.Chrome
ThisBuild / Test / jsEnv := {
  import org.openqa.selenium.chrome.ChromeOptions
  import org.openqa.selenium.firefox.FirefoxOptions
  import org.scalajs.jsenv.selenium.SeleniumJSEnv
  useJSEnv.value match {
    case JSEnv.Chrome =>
      val options = new ChromeOptions()
      options.setHeadless(true)
      new SeleniumJSEnv(options)
    case JSEnv.Firefox =>
      val options = new FirefoxOptions()
      options.setHeadless(true)
      new SeleniumJSEnv(options)
  }
}

lazy val scalajsDomVersion = "2.8.0"
lazy val scalacheckVersion = "1.17.0"
lazy val munitVersion = "1.0.0-M11"

// Source headers keep the original author's copyright.
lazy val originalAuthorHeader =
  headerLicense := Some(HeaderLicense.ALv2("2022", "buntec"))

lazy val root = tlCrossRootProject.aggregate(
  snabbdom,
  examples,
  benchmarks,
  jsFrameworkBenchmark
)

lazy val snabbdom = (project
  .in(file("snabbdom")))
  .enablePlugins(ScalaJSPlugin)
  .settings(
    originalAuthorHeader,
    name := "scala-js-snabbdom",
    libraryDependencies ++= Seq(
      "org.scala-js" %%% "scalajs-dom" % scalajsDomVersion,
      "org.scalameta" %%% "munit" % munitVersion % Test,
      "org.scalacheck" %%% "scalacheck" % scalacheckVersion % Test,
      "org.scala-js" %%% "scala-js-macrotask-executor" % "1.0.0" % Test
    ),
    // The conformance suite always compiles, so that CI keeps it building, but
    // runs only from formal/conformance.sh, which sets SNABBDOM_CONFORMANCE:
    // it is too slow for the normal test run.
    Test / unmanagedSourceDirectories +=
      baseDirectory.value / "src" / "conformance" / "scala",
    Test / testOptions ++= {
      if (sys.env.contains("SNABBDOM_CONFORMANCE")) Nil
      else Seq(Tests.Exclude(Seq("snabbdom.ConformanceSuite")))
    }
  )

lazy val examples = (project
  .in(file("examples")))
  .enablePlugins(ScalaJSPlugin, BundleMonPlugin, NoPublishPlugin)
  .settings(
    originalAuthorHeader,
    name := "scala-js-snabbdom-examples",
    scalaJSUseMainModuleInitializer := true,
    Compile / fastLinkJS / scalaJSLinkerConfig ~= {
      import org.scalajs.linker.interface.ModuleSplitStyle
      _.withModuleKind(ModuleKind.ESModule)
        .withModuleSplitStyle(
          ModuleSplitStyle.SmallModulesFor(
            List("snabbdom.examples")
          )
        )
    }
  )
  .dependsOn(snabbdom)

lazy val benchmarks = (project
  .in(file("benchmarks")))
  .enablePlugins(ScalaJSPlugin, NoPublishPlugin)
  .settings(
    originalAuthorHeader,
    name := "scala-js-snabbdom-benchmarks",
    scalaJSUseMainModuleInitializer := false
  )
  .dependsOn(snabbdom)

lazy val jsFrameworkBenchmark = (project
  .in(file("benchmarks/js-framework-benchmark/scala")))
  .enablePlugins(ScalaJSPlugin, NoPublishPlugin)
  .settings(
    name := "scala-js-snabbdom-js-framework-benchmark",
    scalaJSUseMainModuleInitializer := true
  )
  .dependsOn(snabbdom)
