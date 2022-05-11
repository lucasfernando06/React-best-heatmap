import React, { memo } from "react";
import Container from "./components/Container";

const Column = ({ ...rest }) => {
  return <Container {...rest} />;
};

export default memo(Column);
