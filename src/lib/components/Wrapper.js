import React from "react";

const Wrapper = ({ children, ...rest }) => {
  return <div {...rest}>{children}</div>;
};

export default Wrapper;
