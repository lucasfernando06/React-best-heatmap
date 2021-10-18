import styled from 'styled-components';

export const Container = styled.div`
  position: relative;
  height: 10px;
  width: 10px;
  margin: 2px;
  background-color: #ebedf0;
  border: 1px solid rgba(27, 31, 35, 0.06);
`;

export const Tooltip = styled.div`
  position: absolute;
  min-width: 100px;
  display: flex;
  align-items: center;
  justify-content: center;
  bottom: 200%;
  padding: 8px;
  background-color: rgba(0, 0, 0, .75);
  margin-left: -9px;
  color: #fff;
  z-index: 2;
  border-radius: 5px;
  font-weight: bold;
  ::after {
    content: " ";
    position: absolute;
    top: 100%;
    left: 12%;
    margin-left: -5px;
    border-width: 5px;
    border-style: solid;
    border-color: rgba(0, 0, 0, .75) transparent transparent transparent;
  }
`;