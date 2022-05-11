import React from "react";

import Wrapper from "../../../Wrapper";

const Container = ({ children, ...rest }) => {
  return (
    <Wrapper className="rbh-column-container" {...rest}>
      {children}
    </Wrapper>
  );
};

export default Container;
