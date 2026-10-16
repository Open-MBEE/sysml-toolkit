library package StringPatterns {
	doc
	/*
	 * Lexical patterns of string-encoded attribute definitions.
	 *
	 * A Pattern names, for an attribute definition that specializes ScalarValues::String,
	 * the regular expression every literal value of that type must match in full. It is
	 * applied to the definition itself, as a member of its body, or with `about` to a
	 * definition this library does not own — such as the standard library's ISO 8601
	 * encoding below, whose format its documentation describes in prose. The
	 * `literal-pattern` lint reads these annotations: a string bound to a feature of an
	 * annotated type (a feature value, a constructor or calculation argument) is reported
	 * when it does not match.
	 */
	private import ScalarValues::String;

	metadata def Pattern {
		doc
		/*
		 * The lexical form of a string-encoded attribute definition.
		 *
		 * regex: a regular expression the whole value must match (the lint anchors it).
		 * accepts: an optional broader expression; a value matching it but not regex is
		 *   reported at the lint's reduced severity (info by default) — for a form the
		 *   standard behind the encoding allows but the definition's documentation does
		 *   not spell out.
		 * form: an optional human-readable spelling of the format, quoted in findings in
		 *   place of the regular expression.
		 *
		 * A backslash in a regular expression is doubled inside the string literal: write
		 * "\\." for a literal dot, "[0-9]" rather than a digit class.
		 */
		attribute regex : String;
		attribute accepts : String[0..1];
		attribute form : String[0..1];
	}

	/*
	 * The extended ISO 8601-1 date and time the encoding's documentation prescribes:
	 * ['+' | '-'] YYYY '-' MM '-' DD 'T' hh ':' mm ':' ss ['.' fff [fff]] ('Z' | timezoneOffset),
	 * every component zero-padded, the fraction three or six digits, ss up to 60 for a
	 * leap second. A date alone, a time without seconds, or a date and time without a zone
	 * is accepted at reduced severity: ISO 8601-1 allows the reduced precision, the
	 * encoding's documentation does not. Calendar validity (the day count of a month,
	 * leap years) is beyond a pattern.
	 */
	@Pattern about Time::Iso8601DateTimeEncoding {
		regex = "[+-]?[0-9]{4,}-(0[1-9]|1[0-2])-(0[1-9]|[12][0-9]|3[01])T([01][0-9]|2[0-3]):[0-5][0-9]:([0-5][0-9]|60)(\\.[0-9]{3}([0-9]{3})?)?(Z|[+-]([01][0-9]|2[0-3]):[0-5][0-9])";
		accepts = "[+-]?[0-9]{4,}(-(0[1-9]|1[0-2])(-(0[1-9]|[12][0-9]|3[01]))?)?(T([01][0-9]|2[0-3])(:[0-5][0-9](:([0-5][0-9]|60)(\\.[0-9]+)?)?)?(Z|[+-]([01][0-9]|2[0-3])(:[0-5][0-9])?)?)?";
		form = "YYYY-MM-DDThh:mm:ss[.fff[fff]](Z|±hh:mm)";
	}
}
