import sbt.Keys.libraryDependencies

ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "2.13.12"

ThisBuild / scalacOptions ++= Seq(
  "-opt:l:inline",                    // Inline methods marked with @inline
  "-opt:l:method",                   // Enable cross-method optimizations within the project
  "-optimise",
  //"-opt:l:local",
)

ThisBuild / javaOptions ++= Seq(
  "-Xss128m"
)

lazy val root = (project in file("."))
  .settings(
    name := "factored_solver_scala",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.0.2", // SBT

    libraryDependencies += "org.openjdk.jmh" % "jmh-core" % "1.36",
      libraryDependencies += "org.openjdk.jmh" % "jmh-generator-annprocess" % "1.36"
)


