CREATE FUNCTION polycrack_fdw_handler()
RETURNS fdw_handler
AS 'MODULE_PATHNAME'
LANGUAGE C STRICT;

CREATE FUNCTION polycrack_fdw_validator(text[], oid)
RETURNS void
AS 'MODULE_PATHNAME'
LANGUAGE C STRICT;

CREATE FOREIGN DATA WRAPPER polycrack_fdw
  HANDLER polycrack_fdw_handler
  VALIDATOR polycrack_fdw_validator;
