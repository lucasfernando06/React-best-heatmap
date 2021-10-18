import { Container } from './styles';

const Column = ({
  date,
  index,
  margin = 2,
  ...rest
}) => {
  return (
    <Container {...rest} />
  )
}

export default Column;