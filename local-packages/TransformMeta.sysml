library package TransformMeta {
	metadata def Generated;
	metadata def ProvenanceStore;

	metadata def GeneratedArtifact :> Generated {
		attribute generator;
		attribute generatorVersion;
		attribute parser;
		attribute parserVersion;
		attribute sourceRef;
		attribute sourceDigest;
		attribute generatedDigest;
		attribute libraryDigest;
		attribute optionsDigest;
	}

	metadata def SourceElement :> Generated {
		attribute sourceKey;
		attribute sourcePath;
		attribute semanticDigest;
		attribute structureDigest;
	}

	metadata def TransformState {
		attribute transformId;
		attribute transformerPath;
		attribute scriptDigest;
		attribute forcedSchemaDrift;
	}

	metadata def TransformSource {
		attribute sourceAlias;
		attribute sourceRef;
		attribute inputDigest;
		attribute rowCount;
	}

	metadata def TransformProvenance {
		attribute transformId;
		attribute key;
		attribute rowDigest;
		attribute spellingDigest;
		attribute structureDigest;
		attribute policyDigest;
	}

	metadata def TransformExclusion {
		attribute transformId;
		attribute key;
		attribute transformerPath;
	}
}
