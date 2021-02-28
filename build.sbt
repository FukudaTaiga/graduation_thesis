name := "stringCons"

scalacOptions ++= Seq("-feature", "-unchecked", "-deprecation")
javaOptions in run ++= Seq( "-Xmx2G", "-verbose:gc")
scalaVersion := "2.12.7"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.4"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.4" % "test"
libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.2.26"

assemblyJarName in assembly := "checker.jar"
