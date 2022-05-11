import React from "react";

import Wrapper from "../../../Wrapper";

const Container = ({ children, legend, ...rest }) => {
  return (
    <Wrapper
      className="rbh-wrapper"
      style={{
        marginTop: legend ? 10 : 0,
      }}
      {...rest}
    >
      {children}
    </Wrapper>
  );
};

export default Container;
