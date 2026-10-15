#[test]
#[allow(deprecated)]
fn public_error_inherited_methods_and_io_conversion_preserve_payload() {
    let error = crate::parse_http_date("not a date").unwrap_err();
    let message = "string contains no or an invalid date";

    assert_eq!(error.to_string(), message);
    assert!(std::error::Error::source(&error).is_none());
    assert!(std::error::Error::cause(&error).is_none());
    assert_eq!(
        std::error::Error::description(&error),
        "description() is deprecated; use Display"
    );

    let io_error: std::io::Error = error.into();
    let referenced = io_error
        .get_ref()
        .expect("custom error payload is retained");
    assert_eq!(referenced.to_string(), message);
    assert!(referenced.downcast_ref::<crate::Error>().is_some());

    let boxed = io_error
        .into_inner()
        .expect("custom error payload is extractable");
    let typed = boxed
        .downcast::<crate::Error>()
        .expect("the original Error type is retained");
    assert_eq!(typed.to_string(), message);
}
